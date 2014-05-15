package semper
package silicon
package interfaces

import sil.verifier.VerificationError
import reporting.TraceView
import state.{Store, Heap, State}

/*
 * Results
 */

/* TODO: Extract appropriate interfaces and then move the implementations
 *       outside of the interfaces package.
 */

/* TODO: Make VerificationResult immutable */
abstract class VerificationResult {
	var previous: Option[NonFatalResult] = None

	def isFatal: Boolean
	def &&(other: => VerificationResult): VerificationResult

	def allPrevious: List[VerificationResult] =
		previous match {
			case None => Nil
			case Some(vr) => vr :: vr.allPrevious
		}

	def append(other: NonFatalResult): VerificationResult =
		previous match {
			case None =>
				this.previous = Some(other)
				this
			case Some(vr) =>
				vr.append(other)
		}
}

abstract class FatalResult extends VerificationResult {
	val isFatal = true

	def &&(other: => VerificationResult) = this
}

abstract class NonFatalResult extends VerificationResult {
	val isFatal = false

	/* Attention: Parameter 'other' of '&&' is a function! That is, the following
	 * statements
	 *   println(other)
	 *   println(other)
	 * will invoke the function twice, which might not be what you really want!
	 */
	def &&(other: => VerificationResult): VerificationResult = {
		val r: VerificationResult = other
		r.append(this)
		r
	}
}

case class Success() extends NonFatalResult {
//  context.currentBranch.addResult(this)

  override val toString = "Success"
}

case class Unreachable() extends NonFatalResult {
//  context.currentBranch.addResult(this)

  override val toString = "Unreachable"
}

case class Failure[ST <: Store[ST],
                   H <: Heap[H],
                   S <: State[ST, H, S],
                   TV <: TraceView[TV, ST, H, S]]
                  (message: VerificationError,
                   tv: TV)
		extends FatalResult {

//  tv.addResult(context.currentBranch, this)

  override lazy val toString = message.readableMessage
}
