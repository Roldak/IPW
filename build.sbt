name := "IPW"

version := "0.0.1"

scalaVersion := "2.11.8"

scalacOptions += "-feature"

libraryDependencies += "welder" %% "welder" % "0.1"

libraryDependencies += "org.scalafx" %% "scalafx" % "8.0.102-R11"

libraryDependencies += "net.liftweb" %% "lift-json" % "2.6+"

cancelable in Global := true

fork in run := true