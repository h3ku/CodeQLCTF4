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
