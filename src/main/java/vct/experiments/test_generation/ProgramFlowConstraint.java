package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import vct.antlr4.generated.JavaParser;

import java.util.Arrays;
import java.util.List;
import java.util.StringJoiner;


public class ProgramFlowConstraint {
	enum Type {
		VariableSource,
		VariablesTest,
		VariableTestWhile,
		VariableTestFor,
		VariableTestDoWhile,
		Goal
	}

	public static List<Type> constraints = Arrays.asList(
			Type.VariablesTest,
			Type.VariableTestWhile,
			Type.VariableTestFor,
			Type.VariableTestDoWhile);

	public Type type;
	public ParserRuleContext context;

	public boolean reversed;

	/**
	 * Defaults reversed to false
	 */
	public ProgramFlowConstraint(Type type, ParserRuleContext context) {
		this.type = type;
		this.context = context;
		this.reversed = false;
	}

	public boolean isTest() {
		return constraints.contains(this.type);
	}

	public String repr(JavaParser parser) {
		return new StringJoiner(", ", ProgramFlowConstraint.class.getSimpleName() + "[", "]")
				.add("type=" + type)
				.add("reversed=" + reversed)
				.add("context=" + context.toStringTree(parser))
				.toString();
	}
}
