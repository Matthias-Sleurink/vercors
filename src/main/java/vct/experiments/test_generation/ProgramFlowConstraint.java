package vct.experiments.test_generation;

import org.antlr.v4.runtime.ParserRuleContext;
import vct.antlr4.generated.JavaParser;

import java.util.StringJoiner;

public class ProgramFlowConstraint {
	enum Type {
		VariableSource,
		VariablesTest,
		Goal
	}

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

	public String repr(JavaParser parser) {
		return new StringJoiner(", ", ProgramFlowConstraint.class.getSimpleName() + "[", "]")
				.add("type=" + type)
				.add("reversed=" + reversed)
				.add("context=" + context.toStringTree(parser))
				.toString();
	}
}
