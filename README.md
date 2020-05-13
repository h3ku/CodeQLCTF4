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
