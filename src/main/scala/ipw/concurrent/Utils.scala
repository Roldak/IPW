package ipw.concurrent

protected[ipw] object Utils {
  def async(f: => Unit): Unit = (new Thread {
    override def run = f
  }).start()

  def asyncForever(f: => Unit): Unit = async {
    while (true) f
  }
}