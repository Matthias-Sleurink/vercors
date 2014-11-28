// -*- tab-width:2 ; indent-tabs-mode:nil -*-
package vct.java.printer;

import hre.ast.TrackingOutput;
import hre.ast.TrackingTree;

import java.io.PrintStream;

import org.apache.commons.lang3.StringEscapeUtils;

import vct.col.ast.*;
import vct.col.ast.PrimitiveType.Sort;
import vct.col.util.ASTUtils;
import vct.util.*;
import static hre.System.Abort;
import static hre.System.Debug;
import static hre.System.Warning;

/** 
 * This class contains a pretty printer for Java code.
 * 
 * @author Stefan Blom
 * 
 */
public class JavaPrinter extends AbstractPrinter {
  
  public final JavaDialect dialect;
  protected JavaPrinter(TrackingOutput out,JavaDialect dialect){
    super(JavaSyntax.getJava(dialect),out);
    this.dialect=dialect;
  }

  public void pre_visit(ASTNode node){
    super.pre_visit(node);
    for(NameExpression lbl:node.getLabels()){
      nextExpr();
      lbl.accept(this);
      out.printf(":");
      //out.printf("[");
    }
    if (node.annotated()) for(ASTNode ann:node.annotations()) {
      nextExpr();
      ann.accept(this);
      out.printf(" ");
    }
  }
  
  @Override
  public void visit(ActionBlock ab){
    out.printf("action(");
    nextExpr(); ab.process.accept(this);
    out.printf(",");
    nextExpr(); ab.action.accept(this);
    out.printf(")");
    ab.block.accept(this);
  }
  
  public void post_visit(ASTNode node){
    if (node instanceof BeforeAfterAnnotations && !(node instanceof LoopStatement)){
      BeforeAfterAnnotations baa=(BeforeAfterAnnotations)node;
      if (baa.get_before()!=null && baa.get_before().size()>0 || baa.get_after()!=null && baa.get_after().size()>0){
        out.printf("/*@ ");
        BlockStatement tmp=baa.get_before();
        if (tmp!=null && tmp.size()>0) {
          out.printf("with ");
          tmp.accept(this);
        }
        tmp=baa.get_after();
        if (tmp!=null && tmp.size()>0) {
          out.printf("then ");
          tmp.accept(this);      
        }
        out.printf(" */");
      }
    }
    super.post_visit(node);
  }
  /* TODO: copy to appropriate places
  public void post_visit(ASTNode node){
    if (node.get_before()!=null || node.get_after()!=null){
      out.printf("/*@ ");
      ASTNode tmp=node.get_before();
      if (tmp!=null) {
        out.printf("with ");
        tmp.accept(this);
      }
      tmp=node.get_after();
      if (tmp!=null) {
        out.printf("then ");
        tmp.accept(this);      
      }
      out.printf(" \*\/");
    }
    super.post_visit(node);
  }
  */
  
  @Override 
  public void visit(Axiom ax){
    out.printf("axioms %s: ", ax.name);
    ax.getRule().accept(this);
    out.println(";");
  }

  @Override
  public void visit(AxiomaticDataType adt){
    out.printf("ADT %s [",adt.name);
    String sep="";
    for(DeclarationStatement d:adt.getParameters()){
      out.printf("%s%s",sep,d.name);
      sep=", ";
    }
    out.println("] {");
    out.incrIndent();
    out.println("//constructors");
    for(Method f:adt.constructors()){
      f.accept(this);
    }
    out.println("//mappings");
    for(Method f:adt.mappings()){
      f.accept(this);
    }
    out.println("//axioms");
    for(Axiom ax:adt.axioms()){
      ax.accept(this);
    }
    out.decrIndent();
    out.println("}");
  }
  @Override
  public void visit(ASTSpecial s){
    switch(s.kind){
    case Goto:
      out.print("goto ");
      s.args[0].accept(this);
      //out.println(";");
      break;
    case Label:
      out.print("label ");
      s.args[0].accept(this);
      //out.println(";");
      break;
    case With:
      out.print("WITH");
      s.args[0].accept(this);
      break;
    case Then:
      out.print("THEN");
      s.args[0].accept(this);
      break;
    case Expression:
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;
    case Assert:
      out.print("assert ");
      setExpr();
      s.args[0].accept(this);
      break;
    case Import:
      out.print("import ");
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;    
    case Throw:
      out.print("throw ");
      setExpr();
      s.args[0].accept(this);
      out.println(";");
    case Exhale:
      out.print("exhale ");
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;    
    case Inhale:
      out.print("inhale ");
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;    
    case CreateHistory:
      out.print("create ");
      setExpr();
      s.args[0].accept(this);
      out.printf(",");
      s.args[1].accept(this);
      out.println(";");
      break;    
    case DestroyHistory:
      out.print("destroy ");
      setExpr();
      s.args[0].accept(this);
      out.printf(",");
      s.args[1].accept(this);
      out.printf(",");
      s.args[2].accept(this);
      out.println(";");
      break;    
    case Transfer:
      out.print("transfer ");
      setExpr();
      s.args[0].accept(this);
      out.println(";");
      break;    
    default:
      super.visit(s);
      break;
    }
  }
  
  @Override
  public void visit(ClassType t){
    out.print(t.getFullName());
    ASTNode args[]=t.getArgs();
    if (args.length>0){
      setExpr();
      out.print("<");
      args[0].accept(this);
      for(int i=1;i<args.length;i++){
        out.print(",");
        args[i].accept(this);
      }
      out.print(">");
    }
  }
  public void visit(FunctionType t){
    int N=t.getArity();
    N--;
    for(int i=0;i<N;i++){
      t.getArgument(i).accept(this);
      out.print(",");
    }
    t.getArgument(N).accept(this);
    out.print("->");
    t.getResult().accept(this);
  }

  public void visit(BindingExpression e){
    String binder=null;
    switch(e.binder){
      case FORALL:
        binder="\\forall";
        break;
      case EXISTS:
        binder="\\exists";
        break;
      case STAR:
        binder="\\forall*";
        break;
      case LET:
        binder="\\let";
        break;
      default:
        Abort("binder %s unimplemented",e.binder);
    }
    setExpr();
    out.printf("(%s ",binder);
    int N=e.getDeclCount();
    for(int i=0;i<N;i++){
      if (i>0) out.printf(",");
      DeclarationStatement decl=e.getDeclaration(i);
      decl.getType().accept(this);
      out.printf(" %s",decl.getName());
      if (decl.getInit()!=null){
        out.printf("= ");
        decl.getInit().accept(this);
      }
    }
    out.printf(";");
    if (e.select!=null){
      e.select.accept(this);
      out.printf(";");
    }
    e.main.accept(this);
    out.printf(")");
  }

  public void visit(BlockStatement block){
    out.lnprintf("{");
    out.incrIndent();
    int N=block.getLength();
    for(int i=0;i<N;i++){
      ASTNode statement=block.getStatement(i);
      if (statement.isValidFlag(ASTFlags.GHOST) && statement.isGhost()){
        out.enterGhost();
      }
      statement.accept(this);
      if (self_terminating(statement)){
        out.clearline();
      } else {
        out.lnprintf(";");
      }
      if (statement.isValidFlag(ASTFlags.GHOST) && statement.isGhost()){
        out.leaveGhost();
      }     
    }
    out.decrIndent();
    out.printf("}");
  }

  public void visit(ASTClass cl){
    visit(cl.getContract());
    switch(cl.kind){
    case Plain:
      out.printf("class %s",cl.getName());
      break;
    case Abstract:
      out.printf("abstract class %s",cl.getName());
      break;
    case Interface:
      out.printf("interface %s",cl.getName());
      break;
    case Kernel:
      out.printf("kernel %s",cl.getName());
      break;
    case Record:
      out.printf("record %s",cl.getName());
      break;
    default:
      Abort("unexpected class kind %s",cl.kind);
    }
    if (cl.super_classes.length>0) {
      out.printf("  extends %s",cl.super_classes[0]);
      for(int i=1;i<cl.super_classes.length;i++){
        out.printf(", %s",cl.super_classes[i]);
      }
      out.lnprintf("");
    }
    if (cl.implemented_classes.length>0) {
      out.printf("  implements %s",cl.implemented_classes[0]);
      for(int i=1;i<cl.implemented_classes.length;i++){
        out.printf(", %s",cl.implemented_classes[i]);
      }
      out.lnprintf("");
    }
    out.lnprintf("{");
    out.incrIndent();
    for(ASTNode item:cl){
      if (item.isStatic()){
        if (item instanceof DeclarationStatement) out.printf("static ");
        // else out.println("/* static */");
      }
      item.accept(this);
      out.println("");
    }
    out.decrIndent();
    out.lnprintf("}");    
  }

  @Override
  public void visit(Contract contract) {
    if (contract!=null){
      out.lnprintf("/*@");
      out.incrIndent();
      for (DeclarationStatement d:contract.given){
        out.printf("given ");
        d.accept(this);
        out.lnprintf("");
      }
      for(ASTNode e:ASTUtils.conjuncts(contract.invariant,StandardOperator.Star)){
        out.printf("invariant ");
        nextExpr();
        e.accept(this);
        out.lnprintf(";");
      }
      for(ASTNode e:ASTUtils.conjuncts(contract.pre_condition,StandardOperator.Star)){
        out.printf("requires ");
        nextExpr();
        e.accept(this);
        out.lnprintf(";");
      }
      for (DeclarationStatement d:contract.yields){
        out.printf("yields ");
        d.accept(this);
        out.lnprintf("");
      }
      for(ASTNode e:ASTUtils.conjuncts(contract.post_condition,StandardOperator.Star)){
        out.printf("ensures ");
        nextExpr();
        e.accept(this);
        out.lnprintf(";");
      }
      for (DeclarationStatement d:contract.signals){
        out.printf("signals (");
        d.getType().accept(this);
        out.printf(" %s) ",d.getName());
        nextExpr();
        d.getInit().accept(this);
        out.lnprintf(";");
      }      
      if (contract.modifies!=null){
        out.printf("modifies ");
        if (contract.modifies.length==0){
          out.lnprintf("\\nothing;");
        } else {
          nextExpr();
          contract.modifies[0].accept(this);
          for(int i=1;i<contract.modifies.length;i++){
            out.printf(", ");
            nextExpr();
            contract.modifies[i].accept(this);
          }
          out.lnprintf(";");
        }
      }
      out.decrIndent();
      out.lnprintf("@*/");
    }
  }

  public void visit(DeclarationStatement s){
    ASTNode expr=s.getInit();
    nextExpr();
    s.getType().accept(this);
    out.printf(" %s",s.getName());
    if (expr!=null){
      out.printf("=");
      nextExpr();
      expr.accept(this);
    }
    if (!in_expr) out.printf(";");
  }

  public void visit(Method m){
    int N=m.getArity();
    Type result_type=m.getReturnType();
    String name=m.getName();
    Contract contract=m.getContract();
    boolean predicate=m.getKind()==Method.Kind.Predicate;
    if (predicate){
      if (contract!=null) {
        out.lnprintf("//ignoring contract of predicate");
        System.err.println("ignoring contract of predicate"); 
      }
      out.lnprintf("/*@");
      out.incrIndent();
      out.print("predicate ");
    }
    if (contract!=null && dialect!=JavaDialect.JavaVeriFast && !predicate){
      visit(contract);
    }
    if (!m.isValidFlag(ASTFlags.STATIC)) {
      out.printf("static?? ");
    } else if (m.isStatic()) out.printf("static ");
    if (m.isValidFlag(ASTFlags.FINAL) && m.getFlag(ASTFlags.FINAL)){
      out.printf("final ");
    }
    if (m.getKind()==Method.Kind.Pure){
      out.printf("/*@pure@*/ ");
    }
    if ( m.getParent()!=null
      && m.getParent() instanceof ASTClass
      && ((ASTClass)m.getParent()).getName().equals(name)
    ){
      //out.printf("/*constructor*/");
    } else {
      result_type.accept(this);
      out.printf(" ");
    }
    if (m.getKind()==Method.Kind.Pure) {
       out.printf("/*@ pure */ ");
    }
    out.printf("%s(",name);
    if (N>0) {
      DeclarationStatement args[]=m.getArgs();
      if (args[0].isValidFlag(ASTNode.GHOST) && args[0].isGhost()){ out.printf("/*@ ghost */"); }
      if (args[0].isValidFlag(ASTFlags.OUT_ARG) && args[0].getFlag(ASTFlags.OUT_ARG)){ out.printf("/*@ out */"); }
      m.getArgType(0).accept(this);
      if (N==1 && m.usesVarArgs()){
        out.print(" ...");
      }
      out.printf(" %s",m.getArgument(0));
      for(int i=1;i<N;i++){
        out.printf(",");
        if (args[i].isValidFlag(ASTNode.GHOST) && args[i].isGhost()){ out.printf("/*@ ghost */"); }
        if (args[i].isValidFlag(ASTFlags.OUT_ARG) && args[i].getFlag(ASTFlags.OUT_ARG)){ out.printf("/*@ out */"); }
        m.getArgType(i).accept(this);
        if (i==N-1 && m.usesVarArgs()){
          out.print(" ...");
        }
        out.printf(" %s",m.getArgument(i));
      }
    }
    out.printf(")");
    if (contract!=null && dialect==JavaDialect.JavaVeriFast && !predicate){
      visitVeriFast(contract);
    }
    ASTNode body=m.getBody();
    if (body==null) {
      out.lnprintf(";");
    } else if (body instanceof BlockStatement) {
      body.accept(this);
      out.lnprintf("");
    } else {
      out.printf("=");
      nextExpr();
      body.accept(this);
      out.lnprintf(";");
    }
    if (predicate){
      out.decrIndent();
      out.lnprintf("*/");
    }
  }

  private void visitVeriFast(Contract contract) {
    out.printf("//@ requires ");
    nextExpr();
    contract.pre_condition.accept(this);
    out.lnprintf(";");
    out.printf("//@ ensures ");
    nextExpr();
    contract.post_condition.accept(this);
    out.lnprintf(";");
  }

  public void visit(IfStatement s){
    /* CaseSet conflicts with send/recv in ghost mode! 
    if (s.isValidFlag(ASTNode.GHOST) && s.getFlag(ASTNode.GHOST)){
      int N=s.getCount();
      out.printf ("/*@ CaseSet[");
      for(int i=0;i<N;i++){
        if (i>0) out.printf ("  @         ");
        out.printf("(");
        nextExpr();
        s.getGuard(i).accept(this);
        out.printf(",");
        ASTNode n=s.getStatement(i);
        if (n instanceof BlockStatement){
          BlockStatement block=(BlockStatement)n;
          int M=block.getLength();
          for(int j=0;j<M;j++){
            if(j>0) out.printf(";");
            nextExpr();
            block.getStatement(j).accept(this);
          }
        } else {
          Abort("statement in caseset is not a block at %s",n.getOrigin());
        }
        out.printf(")");
        if(i==N-1){
          out.lnprintf("];");
        } else {
          out.lnprintf(",");
        }
      }
      out.lnprintf("  @ * /");
    } else {*/
      int N=s.getCount();
      out.printf("if (");
      nextExpr();
      s.getGuard(0).accept(this);
      out.print(") ");
      s.getStatement(0).accept(this);
      if (!self_terminating(s.getStatement(0))){
        out.printf(";");
      }
      for(int i=1;i<N;i++){
        if (self_terminating(s.getStatement(i-1))){
          out.printf(" ");
        }
        if (i==N-1 && s.getGuard(i)==IfStatement.else_guard){
          out.printf("else ");
        } else {
          out.printf(" else if (");
          nextExpr();
          s.getGuard(i).accept(this);
          out.lnprintf(") ");
        }
        s.getStatement(i).accept(this);
        if (!self_terminating(s.getStatement(i))){
          out.lnprintf(";");
        }        
      }
    //}
  }

  private boolean self_terminating(ASTNode s) {
    return (s instanceof BlockStatement)
        || (s instanceof IfStatement)
        || (s instanceof LoopStatement)
        || (s instanceof ASTSpecial)
        || (s instanceof DeclarationStatement); 
  }

  public void visit(AssignmentStatement s){
    setExpr();
    s.getLocation().accept(this);
    out.printf("=");
    s.getExpression().accept(this);
  }

  public void visit(ReturnStatement s){
    ASTNode expr=s.getExpression();
    if (expr==null){
      out.lnprintf("return");
    } else {
      out.printf("return ");
      setExpr();
      expr.accept(this);
    }
    if (s.get_after()!=null){
      out.printf("/*@ ");
      out.printf("then ");
      s.get_after().accept(this);
      out.printf(" */");
    }
  }

  public void visit(Lemma l){
      out.printf("/*@ lemma ");
      l.block.accept(this);
      out.lnprintf(" */");
  }
  
  public void visit(OperatorExpression e){
    switch(dialect){
    case JavaVerCors:
      visitVerCors(e);
      break;
    case JavaVeriFast:
      visitVeriFast(e);
      break;
      default:
        super.visit(e);
    }
  }
  private void visitVeriFast(OperatorExpression e){
    switch(e.getOperator()){
    case PointsTo:{
      if (e.getArg(1) instanceof ConstantExpression
      && ((ConstantExpression)e.getArg(1)).equals(1)
      ){
        // [1] is implicit.
      } else {
        out.printf("[");
        e.getArg(1).accept(this);
        out.printf("]");
      }
      e.getArg(0).accept(this);
      out.printf(" |-> ");
      e.getArg(2).accept(this);
      break;
    }
    default:{
      super.visit(e);
    }}
  }
  private void visitVerCors(OperatorExpression e){
    switch(e.getOperator()){
      case NewSilver:{
        out.print("new ");
        // no break on purpose!
      }
      case Tuple:{
        out.print("(");
        String sep="";
        for(ASTNode arg:e.getArguments()){
          out.print(sep);
          sep=",";
          arg.accept(this);
        }
        out.print(")");
        break;
      }
      case Fork:{
        out.printf("fork ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Join:{
        out.printf("join ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Assert:{
        out.printf("assert ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Refute:{
        out.printf("refute ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Continue:{
        out.printf("continue ");
        current_precedence=0;
        ASTNode lbl=e.getArg(0);
        if (lbl!=null){
          setExpr();
          lbl.accept(this);
        }
        break;
      }
      case Assume:{
        out.printf("assume ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case HoarePredicate:{
          out.printf("/*{ ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          out.lnprintf(" }*/");
          break;    	  
      }
      case Lock:{
        ASTNode lock=e.getArg(0);
        setExpr();
        lock.accept(this);
        out.lnprintf(".lock()");
        break;        
      }
      case Unlock:{
        ASTNode lock=e.getArg(0);
        setExpr();
        lock.accept(this);
        out.lnprintf(".unlock()");
        break;        
      }
      case DirectProof:{
        out.printf("//@ proof ");
        current_precedence=0;
        setExpr();
        ASTNode string=e.getArg(0);
        string.accept(this);
        break;
      }
      case Unfold:{
        out.printf("//@ unfold ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Fold:{
          out.printf("//@ fold ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          break;
        }
      case Use:{
        out.printf("//@ use ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Witness:{
        out.printf("//@ witness ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;        
      }
      case Access:{
        out.printf("//@ access ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case Apply:{
          out.printf("//@ apply ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          break;
        }
      case QED:{
          out.printf("//@ qed ");
          current_precedence=0;
          setExpr();
          ASTNode prop=e.getArg(0);
          prop.accept(this);
          break;
        }
      case Open:{
        out.printf("//@ open ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        if (e.get_before()!=null){
          out.printf(" where ");
          e.get_before().accept(this);
          if (e.get_after()!=null){
            out.printf(" then ");
            e.get_after().accept(this);
          }
        }
        break;
      }
      case Close:{
        out.printf("//@ close ");
        current_precedence=0;
        setExpr();
        ASTNode prop=e.getArg(0);
        prop.accept(this);
        break;
      }
      case New:{
        out.printf("new ");
        e.getArg(0).accept(this);
        out.printf("()");
        break;
      }
      case Build:{
        ASTNode args[]=e.getArguments();
        setExpr();
        out.printf("new ");
        args[0].accept(this);
        out.printf("{");
        String sep="";
        for(int i=1;i<args.length;i++){
          out.printf("%s",sep);
          sep=",";
          args[i].accept(this);
        }
        out.printf("}");
        break;
      }
      default:{
        super.visit(e);
      }
    }
  }

  public void visit(LoopStatement s){
    visit(s.getContract());
    ASTNode tmp;
    if (s.getInitBlock()!=null){
      out.printf("for(");
      nextExpr();
       if(s.getInitBlock() instanceof BlockStatement)
      ((BlockStatement)s.getInitBlock()).getStatement(0).accept(this);
       else s.getInitBlock().accept(this);
      out.printf(";");
      nextExpr();
      s.getEntryGuard().accept(this);
      out.printf(";");
      if ((s.getUpdateBlock())!=null){
        nextExpr();
        if(s.getUpdateBlock() instanceof BlockStatement)
        ((BlockStatement)s.getUpdateBlock()).getStatement(0).accept(this);
        else 
        	s.getUpdateBlock().accept(this);
      }
      out.printf(")");
    } else if ((tmp=s.getEntryGuard())!=null) {
      out.printf("while(");
      nextExpr();
      tmp.accept(this);
      out.printf(")");      
    } else {
      out.printf("do");
    }
    if (s.get_before()!=null || s.get_after()!=null){
      out.println("");
      out.println("/*@");
      out.incrIndent();
    }
    if (s.get_before()!=null){
      out.printf("with ");
      s.get_before().accept(this);
      out.println("");
    }
    if (s.get_after()!=null){
      out.printf("then ");
      s.get_after().accept(this);
      out.println("");
    }
    if (s.get_before()!=null || s.get_after()!=null){
      out.decrIndent();
      out.println("@*/");
    }    
    tmp=s.getBody();
    if (!(tmp instanceof BlockStatement)) { out.printf(" "); }
    tmp.accept(this);
    tmp=s.getExitGuard();
    if (tmp!=null){
      out.printf("while(");
      nextExpr();
      tmp.accept(this);
      out.lnprintf(")");      
    }
  }
  
  public void visit(MethodInvokation s){
    super.visit(s);
    //if (s.get_before()!=null){
    //  out.printf("/*@ ");
    //  out.printf("with ");
    //  s.get_before().accept(this);
    //  out.printf(" */");
    //}
    //if (s.get_after()!=null){
    //  out.printf("/*@ ");
    //  out.printf("then ");
    //  s.get_after().accept(this);
    //  out.printf(" */");
    //}    
  }


  public static TrackingTree dump_expr(PrintStream out,JavaDialect dialect,ASTNode node){
    TrackingOutput track_out=new TrackingOutput(out,false);
    JavaPrinter printer=new JavaPrinter(track_out, dialect);
    printer.setExpr();
    node.accept(printer);
    return track_out.close();
  }

  public static TrackingTree dump(PrintStream out,JavaDialect dialect,ProgramUnit program){
    hre.System.Debug("Dumping Java code...");
    try {
      TrackingOutput track_out=new TrackingOutput(out,false);
      JavaPrinter printer=new JavaPrinter(track_out, dialect);
      for(ASTDeclaration item : program.get()){
          item.accept(printer);
      }
      return track_out.close();
    } catch (Exception e) {
      System.out.println("error: ");
      e.printStackTrace();
      throw new Error("abort");
    }
  }

  public static void dump(PrintStream out,JavaDialect dialect, ASTNode cl) {
    TrackingOutput track_out=new TrackingOutput(out,false);
    JavaPrinter printer=new JavaPrinter(track_out,dialect);
    cl.accept(printer);
    track_out.close();    
  }

  public void visit(Dereference e){
    e.object.accept(this);
    out.printf(".%s",e.field);
  }
  
  public void visit(PrimitiveType t){
    switch(t.sort){
      case Pointer:{
        t.getArg(0).accept(this);
        out.printf("*");
        break;
      }
      case Array:
        t.getArg(0).accept(this);
        switch(t.getArgCount()){
        case 1:
            out.printf("[]");
            return;
        case 2:
          out.printf("[/*");
          t.getArg(1).accept(this);
          out.printf("*/]");
          return;
        default:
            Fail("Array type constructor with %d arguments instead of 1 or 2",t.getArgCount());
        }
      case Cell:
        if (t.getArgCount()==2){
          out.printf("cell<");
          t.getArg(0).accept(this);
          out.printf(">[");
          t.getArg(1).accept(this);
          out.printf("]");
          break;
        }
        if (t.getArgCount()!=1){
          Fail("Cell type constructor with %d arguments instead of 1",t.getArgCount());
        }
        out.printf("cell<");
        t.getArg(0).accept(this);
        out.printf(">");
        break;
      case Sequence:
        if (t.getArgCount()!=1){
          Fail("Sequence type constructor with %d arguments instead of 1",t.getArgCount());
        }
        out.printf("seq<");
        t.getArg(0).accept(this);
        out.printf(">");
        break;
      case Set:
        if (t.getArgCount()!=1){
          Fail("Set type constructor with %d arguments instead of 1",t.getArgCount());
        }
        out.printf("set<");
        t.getArg(0).accept(this);
        out.printf(">");
        break;
      case Bag:
        if (t.getArgCount()!=1){
          Fail("Bag type constructor with %d arguments instead of 1",t.getArgCount());
        }
        out.printf("bag<");
        t.getArg(0).accept(this);
        out.printf(">");
        break;
      default:
        super.visit(t);
    }
  }
  
  @Override
  public void visit(ParallelBlock pb){
    if(pb.contract==null){
      Warning("parallel block with null contract!");
    } else {
      visit(pb.contract);
    }
    out.printf("kernel(%s,",pb.decl.getName());
    nextExpr();
    pb.count.accept(this);
    out.printf(")");
    pb.block.accept(this);
  }

  @Override
  public void visit(ParallelBarrier pb){
    if(pb.contract==null){
      Fail("parallel barrier with null contract!");
    } else {
      out.println("barrier{");
      out.incrIndent();
      visit(pb.contract);
      out.decrIndent();
      out.println("}");
    }
  }
  
  public void visit(ConstantExpression ce){
    //if (!in_expr) Abort("constant %s outside of expression for %s",ce,ce.getOrigin());
    if (ce.value instanceof StringValue){
      out.print("\""+StringEscapeUtils.escapeJava(ce.toString())+"\"");
    } else {
      out.print(ce.toString());
    }
  }

  @Override
  public void visit(VariableDeclaration decl){
    decl.basetype.accept(this);
    String sep=" ";
    for(DeclarationStatement d:decl.get()){
      out.print(sep);
      sep=",";
      d.getType().accept(this);
      ASTNode init=d.getInit();
      if (init!=null){
        out.print("=");
        init.accept(this);
      }
    }
    out.println(";");
  }
}

