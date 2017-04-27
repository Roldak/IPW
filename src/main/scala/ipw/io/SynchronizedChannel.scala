package ipw.io

import java.util.concurrent.{BlockingDeque, LinkedBlockingDeque}

object SynchronizedChannel {
  class End[In, Out](private val inDeque: BlockingDeque[In], private val outDeque: BlockingDeque[Out]) {
    def read: In = inDeque.takeFirst()
    def write(v: Out): Unit = outDeque.putLast(v)
  }
  
  def apply[A, B](): (End[A, B], End[B, A]) = {
    val aDeque: BlockingDeque[A] = new LinkedBlockingDeque
    val bDeque: BlockingDeque[B] = new LinkedBlockingDeque
    
    (new End(aDeque, bDeque), new End(bDeque, aDeque))
  }
}