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
