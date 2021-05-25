package vct.silver;

import hre.ast.*;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.*;
import vct.antlr4.generated.JavaParser;
import vct.antlr4.generated.JavaParserBaseListener;
import vct.antlr4.generated.LangJavaLexer;
import vct.col.ast.stmt.decl.ProgramUnit;
import vct.logging.*;
import vct.main.Parsers;
import vct.parsers.ErrorCounter;
import vct.parsers.JavaFindAtLocationListener;
import viper.api.*;

import java.io.*;
import java.nio.file.Path;
import java.text.SimpleDateFormat;
import java.util.*;

import hre.lang.HREError;
import hre.config.Configuration;

import static hre.lang.System.DebugException;
import static hre.lang.System.Output;
import static vct.parsers.JavaFindAtLocationListener.getAtLocation;

public class SilverBackend {
  public static ViperAPI<Origin, ?,?,?,?,?,?>
  getVerifier(String tool) {
    return getViperVerifier(tool);
  }
  
  public static ViperAPI<Origin, ?,?,?,?,?,?>
  getViperVerifier(String tool){
    ViperAPI<Origin, ?,?,?,?,?,?> verifier = null;
    switch(tool.trim()) {
    case "carbon":
      verifier = new CarbonVerifier<>(new HREOrigins());
      break;
    case "silicon":
      verifier = new SiliconVerifier<>(new HREOrigins());
      break;
    case "parser":
      verifier = new SilverImplementation<>(new HREOrigins());
      break;
    default:
      throw new HREError("cannot guess the main class of %s",tool);    
    }
    return verifier;
  }
  
  public static
  PassReport TestSilicon(PassReport given, String tool) {
    ViperAPI<Origin, ?, ?, ?, ?, ?, ?> verifier=getVerifier(tool);
    // We redirect through a new method, because we need to convince java the program type is consistent. The most brief
    // way to capture a  wildcard ("?") type is via a method.
    return TestSilicon(given, tool, verifier);
  }

  public static <Program> PassReport TestSilicon(PassReport given, String tool, ViperAPI<Origin, ?, ?, ?, ?, ?, Program> verifier) {
    //hre.System.Output("verifying with %s backend",silver_module.get());
    ProgramUnit arg=given.getOutput();
    PassReport report=new PassReport(arg);
    report.add(new PassAddVisitor(given));
    report.setOutput(given.getOutput());
    MessageFactory log=new MessageFactory(new PassAddVisitor(report));
    TaskBegin verification=log.begin("Viper verification");

    hre.lang.System.Progress("verifying with %s %s backend", "builtin", tool);
    //verifier.set_detail(Configuration.detailed_errors.get());
    VerCorsViperAPI vercors=VerCorsViperAPI.get();
    Program program = vercors.prog.convert(verifier,arg);
    log.phase(verification,"Backend AST conversion");
    String fname= Configuration.backend_file.get();
    if (fname!=null){
      PrintWriter pw=null;
      try {
        pw = new java.io.PrintWriter(new java.io.File(fname));
        Date now = new Date();
        pw.print("// Generated on ");
        pw.print(new SimpleDateFormat("yyyy-MM-dd").format(now));
        pw.print(" at ");
        pw.println(new SimpleDateFormat("HH:mm:ss").format(now));
        verifier.write_program(pw,program);
      } catch (FileNotFoundException e) {
        DebugException(e);
      } finally {
        if (pw!=null) pw.close();
      }
    }

    Properties settings=new Properties();
    if (tool.startsWith("silicon")){
      //settings.setProperty("smt.soft_timeout",silicon_z3_timeout.get()+"");
    }
    ViperControl control=new ViperControl(log);
    try {
      // Call into Viper to verify!
      List<? extends ViperError<Origin>> rawErrors = verifier.verify(
              Configuration.getZ3Path().toPath(),
              settings,
              program,
              control
      );
      // Put it in a new list so we can add ViperErrors to it ourselves
      List<ViperError<Origin>> errors = new ArrayList<>(rawErrors);

      // Filter SatCheck errors that are to be expected
      // Also collect restOfContractOrigins to determine which contract failed other checks
      // (i.e. maybe an array access was out of bounds, causing an error to be signaled from
      // the contract. this error in turn hides the error from the assert, which is fine,
      // but we need to know when this happens)
      HashSet<AssertOrigin> satCheckAssertsSeen = new HashSet<>();
      HashSet<RestOfContractOrigin> restOfContractsSeen = new HashSet<>();
      errors.removeIf(e -> {
        for (int i = 0; i < e.getExtraCount(); i++) {
          Origin origin = e.getOrigin(i);
          if (origin instanceof AssertOrigin) {
            satCheckAssertsSeen.add((AssertOrigin) origin);
            return true;
          } else if (origin instanceof RestOfContractOrigin) {
            restOfContractsSeen.add((RestOfContractOrigin) origin);
            return true;
          }
        }
        return false;
      });

      // For each satCheckAssert that did not error, if its contract was besides that well formed
      // (i.e. we didn't get an error from the contract inhale),
      // it means the contract is unsatisfiable.
      // Therefore, we warn the user that their contracts are unsound
      HashSet<Origin> expectedSatCheckAsserts = vercors.getSatCheckAsserts();
      for (Origin expectedSatCheckAssert : expectedSatCheckAsserts) {
        AssertOrigin assertOrigin = (AssertOrigin) expectedSatCheckAssert;
        if (!satCheckAssertsSeen.contains(assertOrigin) && !restOfContractsSeen.contains(assertOrigin.restOfContractOrigin)) {
          ViperErrorImpl<Origin> error = new ViperErrorImpl<Origin>(expectedSatCheckAssert, "method.precondition.unsound:method.precondition.false");
          errors.add(error);
        }
      }
			// TODO: method extraction!
	    // This whole thing should be extracted to some sort of "ShouldGenerateTestForNullReturn"

      // We verify somehow that this is indeed an error for which we want to generate a test.
			// Examples 1 and 3 had a PostConditionFailed:AssertionFalse error
			// Annoyingly example 2 has an AssertFailed:AssertionFalse error
	    // These errors are though, also the ones that happen when other errors occur.
	    // We must thus find these errors, and then check if their "Caused by" is indeed a version of \result!=null.

			for (ViperError<Origin> error : errors) {
				Output("Error: ");
				for (int i = 0; i < Integer.MAX_VALUE; i++) {
					try {
						Output("error.getError(%d) = %s", i, error.getError(i));
					} catch (IndexOutOfBoundsException e) {
						break;
					}
				}
				try {
					Output("error.getOrigin(%d) = %s", 0, error.getOrigin(0));
					Output("error.getOrigin(%d).getClass() = %s", 0, error.getOrigin(0).getClass());
					Origin origin = error.getOrigin(0);
					FileOrigin fo;
					if (origin instanceof BranchOrigin) {
						var baseOrigin = ((BranchOrigin) origin).base;
						if (!(baseOrigin instanceof FileOrigin)) {
							Output("%s did not have base of class %s!", origin.getClass(), FileOrigin.class);
							continue; // try the next error
						}
						fo = (FileOrigin) baseOrigin;
					} else if (origin instanceof FileOrigin) {
						fo = (FileOrigin) origin;
					} else {
						continue; // For test generation purposes this branch is not interesting.
					}
					Output("The error location should be here: %s", fo);

					if (fo.getPath() == null) { // TODO: probably never happens.
						Output("Promising origin (%s) had no path!", fo);
						continue;
					}

					// This is of course incredibly racy, but I couldn't get the project to do this in the better way...
					var parsedFile = parsePath(fo.getPath());

					if (parsedFile == null) {
						continue; // This file origin did not bring us a parsable file.
					}

					var cuctx = parsedFile.compilationUnit();

					Output("Interpreted source: %s", cuctx.toStringTree(parsedFile));

					// getFirstColumn appears to be 1 indexed, where the col for the parser rule is 0 indexed.
					var result = getAtLocation(fo.getFirstLine(), fo.getFirstColumn() - 1, cuctx);
					Output("Issue in source result: %s", result.isEmpty() ? "null" : result.get().toStringTree(parsedFile));



				} catch (IndexOutOfBoundsException e) {
					break;
				}
			}


//				Output("Code: %s, sub: %s", vercorsError.code, vercorsError.sub);
//				if (
//						vercorsError.code == VerCorsError.ErrorCode.PostConditionFailed
//								&& vercorsError.sub == VerCorsError.SubCode.AssertionFalse) {
//					// We have found error cases 1 and 3, if these are for ensures \result!=null
//					Output("Cases 1 and 3!");
//				} else if (
//						vercorsError.code == VerCorsError.ErrorCode.AssertFailed
//								&& vercorsError.sub == VerCorsError.SubCode.AssertionFalse
//				) {
//					// we have found error case 2 if this is from ensures \result!=null
//					Output("Case 2!");
//				}

      if (errors.size() == 0) {
        Output("Success!");
      } else {
        Output("Errors! (%d)", errors.size());
        for(ViperError<Origin> e:errors){
          log.error(e);
        }
      }
    } catch (Exception e){
      log.exception(e);
      Output(e.toString());
    } finally {
      control.done();
    }
    log.end(verification);
    return report;
  }

  public static JavaParser parsePath(Path path) {

		File file = path.toFile();
	  Lexer lexer;
	  try {
		  lexer = new LangJavaLexer(CharStreams.fromStream(new FileInputStream(file)));
	  } catch (IOException e) {
		  DebugException(e);
		  Output("Couldn't read input file again. See debug output for more info.");
		  return null;
	  }
	  CommonTokenStream tokens = new CommonTokenStream(lexer);

	  return new JavaParser(tokens);
  }
}
