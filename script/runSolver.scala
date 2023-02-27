/*
 * ----------------------------------------------------------------------------
 * "THE BEER-WARE LICENSE" (Revision 42):
 * <gustav.bjordal@it.uu.se> wrote this file. As long as you retain this notice you
 * can do whatever you want with this stuff. If we meet some day, and you think
 * this stuff is worth it, you can buy me a beer in return.     Gustav Bjordal
 * ----------------------------------------------------------------------------
 */

import scala.io.Source
import java.io._
import java.util.Calendar

import sys.process._

// The script is provided as is. 
// There are multiple TODOS that need to be fixed for the script to run.
// In order for this script to work you need to install your solvers
// according to the MiniZinc 2.2 specifications.


// Version 1.0
object runSolver extends App{


  if(args.length == 0){
    printUsage
    System.exit(1)
  }
  val options = nextOption(Map.empty, args.toList)

  if(options.contains('sat) && options.contains('opt)) {
    println("Error: A problem cannot be sat and opt at the same time.")
    printUsage
    System.exit(1)
  }
  if(!options.contains('sat) && !options.contains('opt)){
    println("Error: You must provide either the -opt or -sat flag!")
    printUsage
    System.exit(1)
  }

  if(options.contains('range) && options.contains('dataFolder)){
    println("Error: cannot iterate over a range and datafiles at the same time.")
    printUsage
    System.exit(1)
  }


  // TODO: The solver names and their printing names must be set to the correct values.
  val solvers = if(options.contains('solvers)){
    options('solvers).asInstanceOf[Array[String]]
  } else Array("org.gecode.gecode@6.1.0", "chuffed", "gurobi", "fzn-oscar-cbls", "picat-sat")
  val solverNames = if(options.contains('solvers)){
    options('solvers).asInstanceOf[Array[String]]
  } else Array("Gecode (CP)", "Chuffed (LCG)", "Gurobi (MIP)", "fzn-oscar-cbls (CBLS)", "Picat (SAT)")

  val outputStream = if(options.contains('output)){
    val outputFile = new File(options('output).asInstanceOf[String])
    new PrintStream(new FileOutputStream(outputFile,true))
  } else System.out


  outputStream.println("% table generation started on " + Calendar.getInstance().getTime())
  // Run solvers over a range
  if(options.contains('range)){
    val rangeArgs = options('range).asInstanceOf[String].split(" ")
    val varName = rangeArgs(0)
    val start = rangeArgs(1).toInt
    val end = rangeArgs(2).toInt
    val inc = rangeArgs.lift(3).getOrElse("1").toInt
    printLatexHeadings("\\texttt{"+varName+"}",outputStream)
    for(i <- start to end by inc) {
      printLatexResultRow("$"+i+"$", runAllSolvers(options.getOrElse('time, 120000).asInstanceOf[Int],
        options('model).asInstanceOf[String],
        "-D" + varName + "=" + i,
        if (options.contains('opt)) "-a" else ""),outputStream)
    }
    // Run solvers over data files
  }else if (options.contains('dataFolder)) {
    val folder = new File(options('dataFolder).asInstanceOf[String])
    val dataFiles = folder.listFiles(new FilenameFilter {
      override def accept(dir: File, name: String): Boolean = {
        !name.startsWith("._") && !dir.isHidden && name.endsWith(".dzn")
      }
    }).sorted
    printLatexHeadings("instance",outputStream)
    for(f <- dataFiles) {
        printLatexResultRow(f.getName.stripSuffix(".dzn").map{case '_' => "\\_"; case c => c}.mkString,
          runAllSolvers(options.getOrElse('time, 120000).asInstanceOf[Int],
            options('model).asInstanceOf[String],
            f.getCanonicalPath,
            if(options.contains('opt)) "-a" else ""),
          outputStream)
      }
  }else{ // Run solvers on model, assuming it is complete
    printLatexHeadings("",outputStream)
    val result = runAllSolvers(options.getOrElse('time, 120000).asInstanceOf[Int],
      options('model).asInstanceOf[String],
      " ",
      if(options.contains('opt)) "-a" else "")
    printLatexResultRow(options('model).asInstanceOf[String],result,outputStream)
  }
  outputStream.println("% printing done on " + Calendar.getInstance().getTime())

  @deprecated("This function should no longer be used", "Version 1.0")
  def outputResults(instanceCaption:String, results:Array[(String,Array[(String,Result)])]) ={
    if(options.contains('output)){
      val outputFile = new File(options('output).asInstanceOf[String])
      printLatexTable(instanceCaption, results, new PrintStream(new FileOutputStream(outputFile,true)))
    }else{
      printLatexTable(instanceCaption, results, System.out)
    }
  }

  def printLatexHeadings(instanceCaption:String, printStream: PrintStream) ={
    printStream.println("Backend")
    for(n <- solverNames) printStream.println("\t&\t\\multicolumn{2}{c}{"+n+"}")
    printStream.println("\\\\")
    for(n <- solverNames.indices) printStream.println("\t\\cmidrule(lr){"+(n*2+2) +"-"+(n*2+3)+"}")
    printStream.print(instanceCaption)
    for(n <- solverNames) printStream.print(" & \\texttt{"+(if(options.contains('vars)) options('vars).asInstanceOf[Array[String]].foldLeft("")((acc,s) => acc + s + ", ") else "")  + (if(options.contains('opt)) "obj" else "status") +"} & time")
    printStream.println("\\\\")
    printStream.println("\\midrule")
  }
  def printLatexResultRow(instance:String, results:Array[(String,Result)], printStream: PrintStream) = {
    printStream.println(instance)
    for((solver, result) <- results){
      if(options.contains('verbose))
        printStream.println("% "+solver)
      printStream.println("\t&\t" + result.getLatexString(options.getOrElse('vars,Array.empty[String]).asInstanceOf[Array[String]],options.contains('opt)))
    }
    printStream.println("\\\\")
  }

  @deprecated("This function should no longer be used", "Version 1.0")
  def printLatexTable(instanceCaption:String, results:Array[(String,Array[(String,Result)])], printStream: PrintStream) = {
    printStream.println("% table generation started on " + Calendar.getInstance().getTime())
    printStream.println("Backend")
    for(n <- solverNames) printStream.println("\t&\t\\multicolumn{2}{c}{"+n+"}")
    printStream.println("\\\\")
    for(n <- solverNames.indices) printStream.println("\t\\cmidrule(lr){"+(n*2+2) +"-"+(n*2+3)+"}")
    printStream.print(instanceCaption)
    for(n <- solverNames) printStream.print(" & \\texttt{"+(if(options.contains('vars)) options('vars).asInstanceOf[Array[String]].foldLeft("")((acc,s) => acc + s + ", ") else "")  + (if(options.contains('opt)) "obj" else "status") +"} & time")
    printStream.println("\\\\")
    printStream.println("\\midrule")
    for((instance,solverResults) <- results){
      printStream.print(instance)
      for((solver, result) <- solverResults){
        if(options.contains('verbose))
          printStream.println("% " + solver)
        printStream.println("\t&\t" + result.getLatexString(options.getOrElse('vars,Array.empty[String]).asInstanceOf[Array[String]],options.contains('opt)))
      }
      printStream.println("\\\\")
    }
    printStream.println("$ printing done on " + Calendar.getInstance().getTime())
  }


  def runAllSolvers(runtimeMs:Int, model:String, data:String, all:String):Array[(String,Result)] = {
    solvers.map( s =>
      (s, runSolver(s, runtimeMs, model, data, all))
    )
  }

  def runSolver(solver:String, runtimeMs:Int, model:String, data:String, all:String):Result = {
    if(options.contains('verbose))
      println("> ---------------- Running solver "+solver+ " ----------------")
    val stdout = new StringBuilder
    val stderr = new StringBuilder

    val currentTime = System.currentTimeMillis

    val runtimeS:Int = (runtimeMs.toFloat/1000).toInt

    // TODO: This path must be fixed:
    val cmd = "timeout " +  ((runtimeS)+30) + " /absolute/path/to/MiniZincIDE/bin/minizinc --no-output-comments --output-mode dzn --output-objective --solver " + solver + " --time-limit " + runtimeMs + "  " + all + " " + model + " " + data
    if(options.contains('verbose))
      println("> Running: " + cmd)
    cmd ! ProcessLogger(stdout append _+"\n", stderr append _+"\n")
    val totalTime = System.currentTimeMillis() - currentTime
    if(options.contains('veryVerbose)) {
      println(stderr)
      println(stdout)
    }
    val parsed = parseOutput(stdout.toString.trim(),totalTime,runtimeMs)
    if(options.contains('verbose))
      println("> parsed: " + parsed)
    parsed
  }


  def parseOutput(output:String, time:Long, timeLimit:Long):Result = {
    if (output.contains("=====UNKNOWN=====")){
      if(time*2 < timeLimit)
        Unknown()
      else
        Unknown()
    }else if(output.contains("=====UNSATISFIABLE=====")){
      Unsat(time)
    }else if(output.contains("=====ERROR=====")){
      Error()
    }else if(!output.contains("----------")) { //careful with this check as it will catch other error messages.
      if(time*2 < timeLimit)
        Unknown()
      else
        Error()
    }else{
      var solutions = output.split("----------")
      val opt = if (solutions.last.contains("==========")){
        solutions = solutions.dropRight(1)
        true
      }else false
      Sol((time).toInt, opt, solutions.last.trim().split("\n").foldLeft(Map.empty[String,String])((acc,str) => {
        val res = str.stripPrefix("% ").split("=")
        acc ++ Map(res.head.trim() -> res.last.trim().stripSuffix(";"))
      }))
    }
  }


  def nextOption(parsed: Map[Symbol,Any], list:List[String]):
  Map[Symbol,Any] = {
    def isSwitch(s:String) = s.charAt(0) == '-'
    list match {
      case "-v" :: tail  =>
        nextOption(parsed ++ Map('verbose -> true), tail)
      case "-vv" :: tail =>
        nextOption(parsed ++ Map('veryVerbose -> true), tail)
      case "-opt" :: tail  =>
        nextOption(parsed ++ Map('opt -> true), tail)
      case "-sat" :: tail  =>
        nextOption(parsed ++ Map('sat -> true), tail)
      case "-t" :: time :: tail if !isSwitch(time) =>
        nextOption(parsed ++ Map('time -> time.toInt), tail)
      case "-m" :: model :: tail if !isSwitch(model)=>
        nextOption(parsed ++ Map('model -> model), tail)
      case "-r" :: range :: tail if !isSwitch(range)=>
        nextOption(parsed ++ Map('range -> range), tail)
      case "-d" :: dataFolder :: tail if !isSwitch(dataFolder)=>
        nextOption(parsed ++ Map('dataFolder -> dataFolder), tail)
      case "-o" :: output :: tail if !isSwitch(output)=>
        nextOption(parsed ++ Map('output -> output), tail)
      case "-vars" :: vars :: tail if !isSwitch(vars)=>
        nextOption(parsed ++ Map('vars -> vars.asInstanceOf[String].split(" ")), tail)
      case "-solvers" :: solvers :: tail if !isSwitch(solvers)=>
        nextOption(parsed ++ Map('solvers -> solvers.asInstanceOf[String].split(" ")), tail)
      case Nil => parsed
      case head :: tail =>
        println("Error parsing option " + head)
        printUsage
        System.exit(1)
        parsed
    }
  }
  def printUsage = {
    val msg = """
-opt              --- Use for optimisation problems
-sat              --- Use for satisfaction problems
-m <mzn file>     --- The model file to run.
-r "<param> <start> <stop> <inc>"
                  --- The range to run experiments over, where
                  --- <param> is the name of the parameter to change.
-d <data folder>
                  --- The name (or path) to a folder containing all
                  --- dzn files to run.
                  --- Do not use -r and -d at the same time !!!
-t <timeout-ms>   --- The time-out in milliseconds.
-o <output file>  --- The file to writeoutput to; will create the
                  --- file if it does not already exist, otherwise
                  --- the results will be appended at the end of
                  --- the file, so consider deleting it first.
-vars "<var1> <var2> ..."
                  --- String of the name of variables to include in
                  --- the output table.
                  --- The objective variable is captured
                  --- automatically.
                  --- This is optional!
-solvers "<solver1> <solver2> ..."
                  --- String of the name of solvers to run.
                  --- This is optional!
-v                --- Verbose output, this will mess up the printing
                  --- unless you specify an output file,
                  --- which you should do anyway...
                  --- Also this will add some comments to the generated table.
"""
    println(msg)
  }
}

trait Result{
  def getLatexString(capturedVars:Array[String],printObj:Boolean):String
}

case class Unsat(time:Long) extends Result {
  override def getLatexString(capturedVars: Array[String], printObj: Boolean): String = {
    capturedVars.foldLeft("")((a,s)=>a+"--,") + "UNSAT" + "\t&\t"+"$"+time+"$"
  }
}
case class Unknown() extends Result {
  override def getLatexString(capturedVars: Array[String], printObj: Boolean): String = {
    capturedVars.foldLeft("")((a,s)=>a+"--,") + "--" + "\t&\tt/o"
  }
}
case class Error() extends Result {
  override def getLatexString(capturedVars: Array[String], printObj: Boolean): String = {
    "ERR" + "\t&\t--"
  }
}
case class Sol(time:Long, isOpt:Boolean, values:Map[String,String]) extends Result {
  override def getLatexString(capturedVars: Array[String], printObj: Boolean): String = {
    capturedVars.foldLeft("")((a,s)=>a+values.getOrElse(s,"??")+",") + (if(printObj) values.getOrElse("_objective","??") else "SAT") + "\t&\t"+(if(isOpt) "$"+time+"$" else "t/o")
  }
}

