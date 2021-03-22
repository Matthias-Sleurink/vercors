package vct.col.rewrite

import hre.ast.MessageOrigin
import hre.lang.System.Output
import vct.col.ast.`type`.ASTReserved
import vct.col.ast.expr.{MethodInvokation, NameExpression, NameExpressionKind, StandardOperator}
import vct.col.ast.generic.ASTNode
import vct.col.ast.stmt.composite.{BlockStatement, LoopStatement, ParallelBlock, ParallelRegion}
import vct.col.ast.stmt.decl.{ASTClass, DeclarationStatement, Method, ProgramUnit}
import vct.col.ast.stmt.terminal.AssignmentStatement
import vct.col.ast.util.{AbstractRewriter, ContractBuilder}
import vct.col.util.SessionChannel
import vct.col.util.SessionUtil.{chanRead, chanWrite, getChanClass, getChansFromBlockStateMent, getThreadClassName, isThreadClassName, runMethodName}

import scala.collection.JavaConversions._

/**
  * Adds the channels to Thread constructors
  * @param source
  */
class SessionThreadConstructors(override val source: ProgramUnit)  extends AbstractRewriter(null, true) {

  var chanMap : Map[String,Set[SessionChannel]] = Map() // A Map threadName -> {(chanName,isWriteValueCall)}

  def addChansToConstructors : ProgramUnit = {
    for(entry <- source.get()) {
      entry match {
        case c : ASTClass => {
          if(isThreadClassName(c.name)) {
            val chans = getChansFromRunMethod(c)
            chanMap += (c.name -> chans)
          }
        }
      }
    }
    rewriteAll
  }

  private def getChansFromRunMethod(c : ASTClass) : Set[SessionChannel] = {
    c.methods().find(_.name == runMethodName) match {
      case Some(runMethod) => {
        val chanMethods = getChansFromBlockStateMent(runMethod.getBody)
        chanMethods.filter(m => m.`object` match {
          case n: NameExpression => true
          case _ => false
        }).map(m => {
          new SessionChannel(m.`object`.asInstanceOf[NameExpression].name, m.method == chanWrite)
        })
      }
      case None => Fail("Session Fail: Thread has no 'run' method"); Set()
    }
  }

  override def visit(m : Method) = {
    if(m.kind == Method.Kind.Constructor && isThreadClassName(m.name)) {
      create.enter()
      create.setOrigin(new MessageOrigin("Generated constructor " + m.name))
      val chans = chanMap.get(m.name).get
      val chanArgs : Set[DeclarationStatement] = chans.map(chan => create.field_decl(chan.getArgChanName(),getChanClass()))
      val newContract = getRoleConstructorContract(chans)
      rewrite(m.getContract,newContract)
      val chanDecls : Array[ASTNode] = chans.map(chan =>
        create.assignment(create.field_name(chan.channel),
                          create.argument_name(chan.getArgChanName()))).toArray
      val threadDecl : Array[ASTNode] = m.getBody match {
          case b : BlockStatement => b.getStatements
        case _ => Fail("Constructor %s must have a BlockStatement body",m.name); Array[ASTNode]()
      }
      val allStats = rewrite(threadDecl) ++ chanDecls
      val args : Array[DeclarationStatement] = rewrite(m.getArgs) ++ chanArgs.toArray[DeclarationStatement]
      val body : BlockStatement = create.block(allStats:_*)
      val myNewMethod = create.method_kind(m.kind,m.getReturnType,newContract.getContract,m.name,args,body)
      create.leave()
      result = myNewMethod
    } else {
      super.visit(m)
    }
  }

  private def getRoleConstructorContract(chans : Set[SessionChannel]) = {
    val contract = new ContractBuilder()
    val reqSentRecvd = chans.map(_.getArgChan().getChanFieldPerm(create))
    val reqNotNull = chans.map(chan =>
      create.expression(StandardOperator.NEQ,
        create.argument_name(chan.getArgChanName()),
        create.reserved_name(ASTReserved.Null)))
    val ensPerm = chans.map(chan =>
      create.expression(StandardOperator.Perm,
        create.field_name(chan.channel),
        create.reserved_name(ASTReserved.ReadPerm)))
    val ensArgEq = chans.map(chan =>
      create.expression(StandardOperator.EQ,
        create.field_name(chan.channel),
        create.argument_name(chan.getArgChanName())))
    val ensSentRecvd = chans.map(_.getChanFieldPerm(create))
    reqSentRecvd.foreach(contract.requires(_))
    reqNotNull.foreach(contract.requires(_))
    ensPerm.foreach(contract.ensures(_))
    ensArgEq.foreach(contract.ensures(_))
    ensSentRecvd.foreach(contract.ensures(_))
    contract
  }



}