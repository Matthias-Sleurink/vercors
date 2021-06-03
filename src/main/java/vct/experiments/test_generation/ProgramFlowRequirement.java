package vct.experiments.test_generation;

import scala.NotImplementedError;
import vct.antlr4.generated.JavaParser;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.StringJoiner;

import static hre.lang.System.Debug;
import static vct.experiments.test_generation.ContextUtil.getName;
import static vct.experiments.test_generation.ProgramFlowConstraint.Type.Goal;
import static vct.experiments.test_generation.TestGenerationUtil.throwForChangedParser;

public class ProgramFlowRequirement {
	enum Type {
		Equality
	}


	// We interpret the parse tree into a requirement that we can reason from
	public static ProgramFlowRequirement makeRequirement(ProgramFlowConstraint constraint) {
		if (constraint == null || constraint.type == Goal) return null;

		var ctx = constraint.context;

		// nonconstraining sources
		if (ctx instanceof JavaParser.FormalParameter0Context) return null;

		if (ctx instanceof JavaParser.VarargsFormalParameter0Context) return null;

		// constraining sources
		if (ctx instanceof JavaParser.VariableDeclarator0Context) {
			Debug("Passed on making ProgramFlowRequirement for " + ctx.getClass() + " due to not being implemented yet.");
			return null;
		}

		// assert
		if (ctx instanceof JavaParser.Statement1Context) {
			var result = makeFrom(((JavaParser.Statement1Context) ctx).expression());
			if (result == null) {
				return null;
			}
			return result.withReversed(constraint.reversed);
		}

		if (ctx instanceof JavaParser.ParExpression0Context) {
			var result = makeFrom(((JavaParser.ParExpression0Context) ctx).expression());
			if (result == null) {
				return null;
			}
			return result.withReversed(constraint.reversed);
		}

		if (ctx instanceof JavaParser.ForControlContext) {
			Debug("Passed on making ProgramFlowRequirement for " + ctx.getClass() + " due to not being implemented yet.");
			return null;
		}

		throwForChangedParser(ctx);
		return null;
	}

	private static ProgramFlowRequirement makeFrom(JavaParser.ExpressionContext ctx) {
		if (ctx instanceof JavaParser.Expression1Context) {
			// This is a bare primary
			return new ProgramFlowRequirement(Type.Equality)
				.withName(getName(ctx))
					.withValue(Boolean.TRUE);
		} else if (ctx instanceof JavaParser.Expression2Context) {
			// This _could be_ a this.name expression...
			var expr2 = (JavaParser.Expression2Context) ctx;

			if (expr2.expression() instanceof JavaParser.Expression1Context &&
					"this".equals(getName(((JavaParser.Expression1Context) expr2.expression()).primary()))) {
				// this is the case of "this.IDENTIFIER"
				return new ProgramFlowRequirement(Type.Equality)
						.withName(getName(expr2.javaIdentifier()))
						.withValue(Boolean.TRUE);
			}
		}
		debugNotImplParse(ctx);
		return null;
	}

	static void debugNotImplParse(Object cause) {
		Debug("Passed on making ProgramFlowRequirement for " + cause.getClass() + " due to not being implemented yet.");
	}

	public ProgramFlowRequirement withReversed(boolean reversed) {
		if (reversed) {
			if (this.value instanceof Boolean) {
				this.value = !(Boolean) this.value;
			}
		}
		return this;
	}

	public ProgramFlowRequirement withValue(Object value) {
		this.value = value;
		return this;
	}

	public ProgramFlowRequirement withName(String name) {
		this.varsInvolved.add(name);
		return this;
	}

	private ProgramFlowRequirement(Type type) {
		this.type = type;
	}

	private final Set<String> varsInvolved = new HashSet<>();

	public Type type;

	public Object value;

	public boolean constrains(String varName) {
		return this.varsInvolved.contains(varName);
	}

	public Object makeValue() {
		if (this.type == Type.Equality) {
			if (this.varsInvolved.size() == 1) {
				return this.value;
			}
		}
		throw new NotImplementedError("Could not makeValue() for this: " + this);
	}

	@Override
	public String toString() {
		return new StringJoiner(", ", ProgramFlowRequirement.class.getSimpleName() + "[", "]")
				.add("varsInvolved=" + Arrays.toString(this.varsInvolved.toArray()))
				.add("type=" + type)
				.add("value=" + value)
				.toString();
	}
}
