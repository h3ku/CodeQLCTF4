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
import  java
import  semmle.code.java.dataflow.DataFlow

/*
Map overrides of isValid method from ConstraintValidator
*/
class  ConstraintValidator  extends  RefType {
	ConstraintValidator() {
		this.getQualifiedName().regexpMatch("javax.validation.ConstraintValidator(.*?)")
	}
}

class  ConstraintValidatorIsValid  extends  Method {
	ConstraintValidatorIsValid() {
		this.getName() = "isValid"  and
		this.getDeclaringType().getASupertype() instanceof  ConstraintValidator
	}
}

predicate  isSource(DataFlow::Node  source) {
	exists(ConstraintValidatorIsValid  isValidMethod|
	source.asParameter() = isValidMethod.getParameter(0)
	)
}

//There has to be a query in scope even when you use Quick Evaluation
select 1
```

This should mark as source nodes the first parameter of the isValid method in classes that implements ConstraintValidator.




