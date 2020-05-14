# CodeQLCTF4

## Step 1: Data flow and taint tracking analysis

### Step 1.1: Sources
The sources of tainted data are the bean properties that go through constraint validation. In the code, these can be found as the first argument of a call to  `ConstraintValidator.isValid(...)`.

Write a CodeQL predicate that identifies these call arguments:

```ql
predicate isSource(DataFlow::Node source) { /* TODO describe source */ }
```

To test your predicate, use the  **Quick Evaluation**  command (Right-click >  `CodeQL: Quick Evaluation`). You should get 8 results.

**Hints:**

-   There is a convenient class  [`RemoteFlowSource`](https://github.com/github/codeql/blob/b6a7ab8bf4a9b1f6e3a95fdfe7be852c03061eab/java/ql/src/semmle/code/java/dataflow/FlowSources.qll#L25)  that tells you when a particular data flow node is obtained from remote user input.
-   Pay attention to get only results that pertain to the project source code.

#### Bonus

_This optional improvement will be taken into account only for distinguishing submissions that are very close in quality and completeness._

You will notice that this implementation will mark every validated bean property as a source of taint. But we want to get only the user-controlled sources. We are not interested in bean properties that an attacker cannot control, such as when the bean comes from unmarshaling an application configuration file.

Consider improving your predicate so we only consider cases where the bean type is bound to user-controllable data such as a JAX-RS endpoint.

### Step 1.1: Sources - Solution
There are multiple ways to implement this, using classes, predicates or straight into the isSource predicate, in my case I decided to map the ConstraintValidator class and the isValid method using classes and the use this classes in the isSource predicate.

```ql
import java
import semmle.code.java.dataflow.DataFlow

/*
Map overrides of isValid method from ConstraintValidator
*/
class ConstraintValidator extends RefType {
	ConstraintValidator() {
		this.getQualifiedName().regexpMatch("javax.validation.ConstraintValidator(.*?)")
	}
}

class ConstraintValidatorIsValid extends Method {
	ConstraintValidatorIsValid() {
		this.getName() = "isValid" and
		this.getDeclaringType().getASupertype() instanceof ConstraintValidator
	}
}

predicate isSource(DataFlow::Node source) {
	exists(ConstraintValidatorIsValid isValidMethod |
		source.asParameter() = isValidMethod.getParameter(0)
	)
}

//There has to be a query in scope even when you use Quick Evaluation
select 1
```

A quick evaluation of isSource should mark as source nodes the first parameter of the isValid method in classes that implements ConstraintValidator.


### Step 1.2: Sink

The injection sinks we are considering occur as the first argument of a call to  `ConstraintValidatorContext.buildConstraintViolationWithTemplate(...)`.

Write a CodeQL predicate to identify these sinks.
```ql
predicate isSink(DataFlow::Node sink) { /* TODO describe sink */ }
```
Quick evaluation of your predicate should give you 5 results.

### Step 1.2: Sink - Solution
Same as before there are quite a few ways to implement this, in this case I decided to go with a class to map the method BuildConstraintViolationWithTemplate from ConstraintValidatorContext and then put the rest of the login in the isSink predicate.

```ql
import java
import semmle.code.java.dataflow.DataFlow

/**
Map ConstraintValidatorContext.BuildConstraintViolationWithTemplate.
*/
class BuildConstraintViolationWithTemplate extends Method {
	BuildConstraintViolationWithTemplate() {
		this.hasName("buildConstraintViolationWithTemplate") and
		this.getDeclaringType().hasName("ConstraintValidatorContext")
	}
}

predicate isSink(DataFlow::Node sink) {
	exists(MethodAccess  callTobuildConstraintViolationWithTemplate |
		callTobuildConstraintViolationWithTemplate.getMethod() instanceof BuildConstraintViolationWithTemplate and
		sink.asExpr() = callTobuildConstraintViolationWithTemplate.getArgument(0)
	)
}

//There has to be a query in scope even when you use Quick Evaluation
select 1
```

A quick evaluation of isSink should mark as sink nodes the first argument of calls to the method ConstraintValidatorContext.buildConstraintViolationWithTemplate() 


### Step 1.3: TaintTracking configuration
Before going any further, we recommend that you quick-eval your  `isSource`  and  `isSink`  predicates to make sure both are matching the issue described above in  `SchedulingConstraintSetValidator.java`. This case will be our main target issue for the rest of this challenge.

All done? Ok, so now let's find this vulnerable path by tracking the tainted data!

You'll need to create a taint tracking configuration as explained in the  [CodeQL documentation](https://help.semmle.com/QL/learn-ql/java/dataflow.html#global-data-flow). Fill in the template below with your definitions of  `isSource`  and  `isSink`, and a nicer name. The predicate  `hasFlowPath`  will hold for any path through which data can flow from your sources to your sinks. As you checked that your predicates give you the correct sources and sinks, we'll get our vulnerability.

```ql
/** @kind path-problem */
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

class MyTaintTrackingConfig extends TaintTracking::Configuration {
    MyTaintTrackingConfig() { this = "MyTaintTrackingConfig" }

    override predicate isSource(DataFlow::Node source) { 
        // TODO 
    }

    override predicate isSink(DataFlow::Node sink) { 
        // TODO 
    }
}

from MyTaintTrackingConfig cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
```

Run your query using the command  `CodeQL: Run Query`  (either in the Command Palette or the right-click menu). It should give you ...  **0 results**! Ok, this is disappointing! But don't give up just now.

### Step 1.3: TaintTracking configuration - Solution
Not much to say for this one, just copy paste the previous steps into the provided template.

```ql
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

/**
Map overrides of isValid method from ConstraintValidator
*/
class ConstraintValidator extends RefType {
	ConstraintValidator() {
		this.getQualifiedName().regexpMatch("javax.validation.ConstraintValidator(.*?)")
	}
}

class ConstraintValidatorIsValid extends Method {
	ConstraintValidatorIsValid() {
		this.getName() = "isValid" and
		this.getDeclaringType().getASupertype() instanceof  ConstraintValidator
	}
}

/**
Map ConstraintValidatorContext.BuildConstraintViolationWithTemplate
*/
class BuildConstraintViolationWithTemplate extends Method {
	BuildConstraintViolationWithTemplate() {
		this.hasName("buildConstraintViolationWithTemplate") and
		this.getDeclaringType().hasName("ConstraintValidatorContext")
	}
}

class UnsafeErrorGeneration extends TaintTracking::Configuration {
	UnsafeErrorGeneration() { this = "UnsafeErrorGeneration" }
	
	override predicate isSource(DataFlow::Node source) {
		exists(ConstraintValidatorIsValid isValidMethod|
			source.asParameter() = isValidMethod.getParameter(0)
		)
	}
	
	override predicate isSink(DataFlow::Node sink) {
		exists(MethodAccess callTobuildConstraintViolationWithTemplate |
			callTobuildConstraintViolationWithTemplate.getMethod() instanceof  BuildConstraintViolationWithTemplate  and
			sink.asExpr() = callTobuildConstraintViolationWithTemplate.getArgument(0)
		)
	}
}

from UnsafeErrorGeneration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
```


### Step 1.4: Partial Flow to the rescue

When developing taint tracking queries, we may find ourselves in this situation very often. Why aren't we getting a hit?

We identified the source and the sink, so this suggests that our analysis is missing a step along the path from the source to the sink.

CodeQL's Java libraries can help us find the missing gaps with the  **partial data flow**  debugging mechanism. This feature allows you to look for flows from a given source to any possible sink, leaving the sink unconstrained while limiting the number of steps away from the source to search for. So you can use this feature to track the flow of tainted data from your source to all possible sinks, and see where the flow stops being tracked further.

Create a debugging query that uses the  [`hasPartialFlow`  predicate](https://github.com/github/codeql/blob/master/java/ql/src/semmle/code/java/dataflow/internal/DataFlowImpl.qll#L124). You can use the template below.

```ql
/** @kind path-problem */
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PartialPathGraph // this is different!

class MyTaintTrackingConfig extends TaintTracking::Configuration {
    MyTaintTrackingConfig() { ... } // same as before
    override predicate isSource(DataFlow::Node source) { ... } // same as before
    override predicate isSink(DataFlow::Node sink) { ... } // same as before
    override int explorationLimit() { result =  10} // this is different!
}
from MyTaintTrackingConfig cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
  cfg.hasPartialFlow(source, sink, _) and
  source.getNode() = ... // TODO restrict to the one source we are interested in, for ease of debugging
select sink, source, sink, "Partial flow from unsanitized user data"

predicate partial_flow(PartialPathNode n, Node src, int dist) {
  exists(MyTaintTrackingConfig conf, PartialPathNode source |
    conf.hasPartialFlow(source, n, dist) and
    src = source.getNode() and
    source =  // TODO - restrict to THE source we are interested in
  )
}
```

Run your modified query to explore the flow of data and detect where the path stops.

**Tips:**

-   Still don't get any results? Make sure to read the documentation of the  `hasPartialFlow`  predicate carefully and adapt your taint tracking configuration accordingly.
-   You can add other variables that you'd need for your analysis using the  `exists`  keyword, or as parameters of your  `from`  clause. For example, you could restrict to only source and sink nodes in a particular enclosing function or file location.This will help you quickly filter your results to only the ones your interested in.

### Step 1.4: Partial Flow to the rescue - Solution
Again the changes are quite simple for this step, just adapt the previous query to the provided template and add some filters by filenames.

```ql
/** @kind path-problem */
import  java
import  semmle.code.java.dataflow.TaintTracking
import  DataFlow::PartialPathGraph  // this is different!

/**
Map overrides of isValid method from ConstraintValidator
*/
class ConstraintValidator extends RefType {
	ConstraintValidator() {
		this.getQualifiedName().regexpMatch("javax.validation.ConstraintValidator(.*?)")
	}
}

class ConstraintValidatorIsValid extends Method {
	ConstraintValidatorIsValid() {
		this.getName() = "isValid"  and
		this.getDeclaringType().getASupertype() instanceof  ConstraintValidator
	}
}

/**
Map ConstraintValidatorContext.BuildConstraintViolationWithTemplate
*/
class BuildConstraintViolationWithTemplate extends Method {
	BuildConstraintViolationWithTemplate() {
		this.hasName("buildConstraintViolationWithTemplate") and
		this.getDeclaringType().hasName("ConstraintValidatorContext")
	}
}

class UnsafeErrorGeneration extends TaintTracking::Configuration {
	UnsafeErrorGeneration() { this = "UnsafeErrorGeneration" }
	
	override predicate isSource(DataFlow::Node source) {
		exists(ConstraintValidatorIsValid isValidMethod|
			source.asParameter() = isValidMethod.getParameter(0)
		)
	}
	
	override predicate isSink(DataFlow::Node sink) {
		exists(MethodAccess callTobuildConstraintViolationWithTemplate |
			callTobuildConstraintViolationWithTemplate.getMethod() instanceof  BuildConstraintViolationWithTemplate  and
			sink.asExpr() = callTobuildConstraintViolationWithTemplate.getArgument(0)
		)
	}

	override int explorationLimit() { result = 10}
}

from UnsafeErrorGeneration cfg, DataFlow::PartialPathNode  source, DataFlow::PartialPathNode sink
where
	cfg.hasPartialFlow(source, sink, _) and
	source.getNode().getLocation().getFile().getStem() = "SchedulingConstraintSetValidator"  //Filter to only source nodes in the file we are interested in
select sink, source, sink, "Partial flow from unsanitized usedr data"
```

The only substantial change is the addition in the where clausure to filter by the file name that we are interested in, using ``source.getNode().getLocation().getFile().getStem() = "SchedulingConstraintSetValidator"``, this way it becomes easier to work with resulting partial flows.


### Step 1.5: Identifying a missing taint step
You must have found that CodeQL does not propagate taint through getters like  `container.getHardConstraints`  and  `container.getSoftConstraints`. Can you guess why this default behaviour was implemented?

### Step 1.5: Identifying a missing taint step - Solution
My understanding of this os that CodeQL doesn't propagate taint through getters to prevent false positives. Imagine for example that we have an object, some of the properties of the object are user-controlled, but some others are not. Now we have a sink in the first parameter of a function that receives a call to a getter of our object, for CodeQL is not possible to know if the getter of this object is obtaining the properties that we are interested in (The user-controlled ones) or just any of the other random properties, because of this CodeQL decide to not propagate through getters unless you specify it.


### Step 1.6: Adding additional taint steps

Now you know that some taint steps are missing. This is because the analysis is careful by default, and tries not to give you extra flow that may lead to false positives. Now you need to tell your taint tracking configuration that tainted data can be propagated by certain code patterns.

CodeQL allows you to declare additional taint steps in a specific taint tracking configuration, as shown  [in this example](https://github.com/github/codeql/blob/master/docs/language/ql-training/java/global-data-flow-java.rst#defining-additional-taint-steps).

However, we'll use an even more general approach, which allows us to add taint steps globally, so that they can be picked up by several taint tracking configurations (and potentially reused in many queries). For this you just have to extend the class  [TaintTracking::AdditionalTaintStep](https://github.com/github/codeql/blob/bc7163aa68017f93c25ec7423044727a5d785142/java/ql/src/semmle/code/java/dataflow/internal/TaintTrackingUtil.qll#L67)  and implement the  `step`  predicate. The  `step`  predicate should hold true when tainted data flows from  `node1`  to  `node2`.

Run your  **original**  query again after adding a taint step. Did you get the expected results? Still no.

Re-run your  **partial flow**  query again, to find where you lost track of your tainted data this time.

**Hints:**  In the  `step`  predicate you should indicate that the 2 nodes are 2 elements of a  `MethodAccess`: one will be an argument and one will be the return value found at the call site.

### Step 1.6: Adding additional taint steps - Solution
This is probably one of the parts that I enjoyed the most since I didn't know about custom taint tracking steps before.

The implementation is quite simple, we create a new class that extends AdditionalTaintStep that contains a step predicate, this predicate expect two nodes as arguments that we will call node1 and node2.
We are trying to map something like this ```sink(source.getSoftConstraints())```
So in this case we need to tell the taint tracking configuration that the node1 is the qualifier of a method access, since `getSoftConstraints` is a method of the source object and the second node will be the return of this method call. 
This will consider a call to any method of source a sink, and even that this can be interesting for manual audits it can introduce a lot of false positives as explained in the previous section, so we need to add a filter for the methods that we are interested in, in this case `getSoftConstraints` and `keySet`.

```ql
class CustomSteps extends TaintTracking::AdditionalTaintStep {
	override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
		exists(MethodAccess ma|
			(ma.getMethod().hasName("getSoftConstraints") or
			ma.getMethod().hasName("keySet"))
			and
			node1.asExpr() = ma.getQualifier() and
			node2.asExpr() = ma
		)
	}
}
```

If we run the entire query we are not going to get any results, since we need to add some more custom steps as can be seen in the following section, but this custom step can be tried out using Quick Evaluation.


### Step 1.7: Adding taint steps through a constructor

Repeat the process above with all the methods that interrupt the taint tracking, until your partial flow predicate takes you finally to the call to constructor  `HashSet`.

Now you observe that CodeQL does not propagate through the  `HashSet`  constructor. Write an additional taint step for this and re-run your query.

### Step 1.7: Adding taint steps through a constructor - Solution

Now that our query propagates through some methods of the source we have another problem, by default the taint tracking don't propagate through an instantiation of a new object. So we need to create a step predicate where the node1 will be the first argument of a call to the constructor of hashset and the node2 will be the result of this constructor call.

```ql
class CustomSteps2 extends TaintTracking::AdditionalTaintStep {
	override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
		exists(ConstructorCall newHashSet |
			newHashSet.getConstructor().hasName("HashSet<String>") and
			node1.asExpr() = newHashSet.getArgument(0) and
			node2.asExpr() = newHashSet
		)
	}
}
```

### Step 1.8: Finish line for our first issue

Repeat the process above by adding more additional taint steps as needed, until your tainted data flows to the argument of the call to  `buildConstraintViolationWithTemplate`. Run your query.

Hurray! The issue should be reported now!

### Step 1.8: Finish line for our first issue - Solution
Just mix all the previous steps all together.

```ql
import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

/**
Map overrides of isValid method from ConstraintValidator
*/
class ConstraintValidator extends RefType {
  ConstraintValidator() {
      this.getQualifiedName().regexpMatch("javax.validation.ConstraintValidator(.*?)")
  }
}

class ConstraintValidatorIsValid extends Method {
    ConstraintValidatorIsValid() {
        this.getName() = "isValid" and
        this.getDeclaringType().getASupertype() instanceof ConstraintValidator
    }
}

/**
Map ConstraintValidatorContext.BuildConstraintViolationWithTemplate
*/
class BuildConstraintViolationWithTemplate extends Method {
	BuildConstraintViolationWithTemplate() {
		this.hasName("buildConstraintViolationWithTemplate") and
		this.getDeclaringType().hasName("ConstraintValidatorContext")
	}
}

class UnsafeErrorGeneration extends TaintTracking::Configuration {
    UnsafeErrorGeneration() { this = "UnsafeErrorGeneration" }

    override predicate isSource(DataFlow::Node source) { 
        exists(ConstraintValidatorIsValid isValidMethod|
        source.asParameter() = isValidMethod.getParameter(0)
    )
    }

    override predicate isSink(DataFlow::Node sink) { 
		exists(MethodAccess callTobuildConstraintViolationWithTemplate |
			callTobuildConstraintViolationWithTemplate.getMethod() instanceof  BuildConstraintViolationWithTemplate  and
			sink.asExpr() = callTobuildConstraintViolationWithTemplate.getArgument(0)
		)
    }
}

class CustomSteps extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
        exists(MethodAccess ma|
            (ma.getMethod().hasName("getSoftConstraints")  or
            ma.getMethod().hasName("keySet"))
            and
            node1.asExpr() = ma.getQualifier() and
            node2.asExpr() = ma
        ) 
    }
}

class CustomSteps2 extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
        exists(ConstructorCall newHashSet |
            newHashSet.getConstructor().hasName("HashSet<String>") and
            node1.asExpr() = newHashSet.getArgument(0) and
            node2.asExpr() = newHashSet
        ) 
    }
}

from UnsafeErrorGeneration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
```
