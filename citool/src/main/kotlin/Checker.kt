package de.uka.ilkd.key

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import com.github.ajalt.clikt.parameters.types.int
import de.uka.ilkd.key.api.KeYApi
import de.uka.ilkd.key.api.ProofManagementApi
import de.uka.ilkd.key.control.AbstractProofControl
import de.uka.ilkd.key.control.AbstractUserInterfaceControl
import de.uka.ilkd.key.control.KeYEnvironment
import de.uka.ilkd.key.control.UserInterfaceControl
import de.uka.ilkd.key.logic.PosInOccurrence
import de.uka.ilkd.key.macros.*
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine
import de.uka.ilkd.key.parser.Location
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.proof.Proof
import de.uka.ilkd.key.proof.Statistics
import de.uka.ilkd.key.prover.ProverTaskListener
import de.uka.ilkd.key.settings.ChoiceSettings
import de.uka.ilkd.key.settings.ProofSettings
import de.uka.ilkd.key.speclang.Contract
import de.uka.ilkd.key.util.KeYConstants
import de.uka.ilkd.key.util.MiscTools
import org.key_project.util.collection.ImmutableList
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.io.File
import java.io.FileInputStream
import java.io.IOException
import java.util.*
import java.util.zip.GZIPInputStream
import kotlin.system.exitProcess
import kotlin.system.measureTimeMillis


const val ESC = 27.toChar()
const val RED = 31
const val GREEN = 32
const val YELLOW = 33
const val BLUE = 34
const val MAGENTA = 35
const val CYAN = 36
fun color(s: Any, c: Int) = "${ESC}[${c}m$s${ESC}[0m"

private inline fun <reified T> logger(): Logger {
    return LoggerFactory.getLogger(T::class.java)
}

/**
 * A small interface for a checker scripts
 * @author Alexander Weigl
 * @version 1 (21.11.19)
 */
class Checker : CliktCommand() {
    val logger = logger<Checker>()

    private val statistics = TreeMap<String, Any>()

    val junitXmlOutput by option("--xml-output").file()

    val enableMeasuring: Boolean by option(
        "--measuring",
        help = "try to measure proof coverage"
    ).flag()

    val includes by option(
        help = "defines additional key files to be included"
    ).multiple()

    val autoModeStep by option(
        "--auto-mode-max-step", metavar = "INT",
        help = "maximal amount of steps in auto-mode [default:10000]"
    )
        .int().default(10000)

    val verbose by option("-v", "--verbose", help = "verbose output")
        .flag("--no-verbose")

    val debug by option("-d", "--debug", help = "more verbose output")
        .flag("--no-debug")


    val readContractNames by option(
        "--read-contract-names-from-file",
        help = "if set, the contract names are read from the proof file contents"
    )
        .flag()

    val disableAutoMode by option(
        "--no-auto-mode",
        help = "If set, only contracts with a proof script or proof are replayed."
    )
        .flag()

    val statisticsFile: File? by option(
        "-s",
        "--statistics",
        help = "if set, JSON files with proof statistics are written"
    )
        .file()

    val dryRun by option(
        "--dry-run",
        help = "skipping the proof reloading, scripts execution and auto mode." +
                " Useful for finding the contract names"
    ).flag()

    val classpath by option(
        "--classpath", "-cp",
        help = "additional classpaths"
    ).multiple()

    val bootClassPath by option(
        "--bootClassPath", "-bcp",
        help = "set the bootclasspath"
    )

    val onlyContractsRaw by option(
        "--contract",
        help = "whitelist contracts by their names"
    )
        .multiple()

    val onlyContractsFiles by option(
            "--contracts-file",
            help = "whitelist contracts by their names from a file"
    )
            .multiple()

    val onlyContractsFilter by option(
            "--contracts-filter",
            help = "filter contracts by their names using a regex"
    )

    val forbidContractsRaw by option(
        "--forbid-contact",
        help = "forbid contracts by their name"
    )
        .multiple()

    val forbidContractsFiles by option(
            "--forbid-contracts-file",
            help = "forbid contracts by their names from a file"
    )
            .multiple()

    val inputFile by argument(
        "JAVA-KEY-FILE",
        help = "key, java or a folder"
    )
        .multiple(true)

    val proofPath by option(
        "--proof-path",
        help = "folders to look for proofs and script files"
    )
        .multiple()

    private var choiceSettings: ChoiceSettings? = null

    private fun initEnvironment() {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            val env: KeYEnvironment<*> = KeYEnvironment.load(File("."), null, null, null)
            env.dispose()
        }
        choiceSettings = ProofSettings.DEFAULT_SETTINGS.choiceSettings
    }

    var errors = 0

    var testSuites = TestSuites()

    override fun run() {
        logger.info("KeY version: ${KeYConstants.VERSION}")
        logger.info("KeY internal: ${KeYConstants.INTERNAL_VERSION}")
        logger.info("Copyright: ${KeYConstants.COPYRIGHT}")
        logger.info("More information at: https://formal.iti.kit.edu/weigl/ci-tool/")

        if (debug) {
            logger.info("Proof files and Sripts found: ")
            proofFileCandidates.forEach {
                logger.info(it.absolutePath)
            }
        }

        testSuites.name = inputFile.joinToString(" ")

        val onlyContracts =
            (onlyContractsFiles.flatMap {
                File(it).readLines()
            } + onlyContractsRaw)
                    .map { it.trim() }
                    .filter { it.isNotEmpty() && !it.startsWith("#") }
                    .toHashSet()

        val forbidContracts = (forbidContractsFiles.flatMap {
            File(it).readLines()
        } + forbidContractsRaw)
                .map { it.trim() }
                .filter { it.isNotEmpty() && !it.startsWith("#")}
                .toHashSet()

        inputFile.forEach { run(it, onlyContracts, forbidContracts) }

        statisticsFile?.writeText(obj2json(statistics))

        junitXmlOutput?.let { file ->
            file.bufferedWriter().use {
                testSuites.writeXml(it)
            }
        }

        exitProcess(errors)
    }

    fun run(inputFile: String, onlyContracts: HashSet<String>, forbidContracts: HashSet<String>) {
        logger.info("Start with `$inputFile`")
        val pm = KeYApi.loadProof(File(inputFile),
            classpath.map { File(it) },
            bootClassPath?.let { File(it) },
            includes.map { File(it) })

        // println(onlyContractsFilter)
        // pm.proofContracts
        //         .sortedWith(
        //                 compareBy<Contract> {
        //                     it.name.substringBeforeLast('.').substringAfterLast('.')
        //                 }.thenBy { it.name })
        //         .forEach { println(it.name) }
        // println()

        logger.info("Found: ${pm.proofContracts.size} contracts")
        val filter = onlyContractsFilter?.let { Regex(it) }
        val (contracts, ignoredContracts) = pm.proofContracts
            .filter {
                (onlyContracts.isEmpty() || it.name in onlyContracts) &&
                        (filter == null || filter.matches(it.name)) }
            .sortedBy { it.name }
            .partition { it.name !in forbidContracts }

        logger.info("Check: ${contracts.size} contracts (by only contracts)")

        var successful = 0
        var ignored = 0
        var failure = 0

        val testSuite = testSuites.newTestSuite(inputFile)
        ProofSettings.DEFAULT_SETTINGS.properties.forEach { t, u ->
            testSuite.properties[t.toString()] = u
        }

        for (c in contracts) {
            val testCase = testSuite.newTestCase(c.name)
            logger.info("Contract: `${c.name}`")
            when {
                dryRun -> {
                    testCase.result = TestCaseKind.Skipped("Contract skipped by `--dry-run`.")
                    ignored++
                }
                else -> {
                    when (runContract(pm, c)) {
                        ProofState.Success -> successful++
                        ProofState.Failed -> {
                            testCase.result = TestCaseKind.Failure("Proof not closeable.")
                            failure++
                        }
                        ProofState.Skipped -> ignored++
                    }
                }
            }
        }
        logger.info(
            "Summary for $inputFile: " +
                    "(successful/ignored/failure) " +
                    "(${color(successful, GREEN)}/${color(ignored, BLUE)}/${color(failure, RED)})"
        )
        if (failure != 0)
            logger.error("$inputFile failed!")
    }

    private fun runContract(pm: ProofManagementApi, contract: Contract): ProofState {
        ProofSettings.DEFAULT_SETTINGS.strategySettings.maxSteps = autoModeStep
        val proofFile = findProofFile(contract.name)

        val closed = if (proofFile != null) {
            logger.info("Proof found: $proofFile. Try loading.")
            loadProof(proofFile)
        } else {
            val proofApi = pm.startProof(contract)
            val proof = proofApi.proof
            require(proof != null)
            val scriptFile = findScriptFile(contract.name)
            proof.settings?.strategySettings?.maxSteps = autoModeStep
            val ui = proofApi.env.ui as AbstractUserInterfaceControl
            val pc = proofApi.env.proofControl as AbstractProofControl
            try {
                if (scriptFile != null) {
                    logger.info("Script found: $scriptFile. Try proving.")
                    loadScript(ui, proof, scriptFile)
                } else {
                    if (verbose)
                        logger.info("No proof or script found. Fallback to auto-mode.")
                    if (disableAutoMode) {
                        logger.warn("Proof skipped because to `--no-auto-mode' switch is set.")
                        ProofState.Skipped
                    } else {
                        runAutoMode(pc, proof)
                    }
                }
            } finally {
                proof.dispose()
            }
        }

        when (closed) {
            ProofState.Success -> logger.info(color("✔ Proof closed.", GREEN))
            ProofState.Skipped -> logger.warn(color("! Proof skipped.", YELLOW))
            ProofState.Failed -> {
                errors++
                logger.error(color("✘ Proof open.", RED))
            }
        }

        return closed
    }

    private fun runAutoMode(proofControl: AbstractProofControl, proof: Proof): ProofState {
        val time = measureTimeMillis {
            if (enableMeasuring) {
                val mm = MeasuringMacro()
                proofControl.runMacro(proof.root(), mm, null)
                proofControl.waitWhileAutoMode()
                logger.info("Proof has open/closed before: ${mm.before}")
                logger.info("Proof has open/closed after: ${mm.after}")
            } else {
                proofControl.startAndWaitForAutoMode(proof)
            }
        }
        if (verbose) {
            logger.info("Auto-mode took ${time / 1000.0} seconds.")
        }
        printStatistics(proof)
        return if (proof.closed()) ProofState.Success else ProofState.Failed
    }

    private fun loadScript(ui: AbstractUserInterfaceControl, proof: Proof, scriptFile: File): ProofState {
        val script = scriptFile.readText()
        val engine = ProofScriptEngine(script, Location(scriptFile.toURL(), 1, 1))
        val time = measureTimeMillis {
            engine.execute(ui, proof)
        }
        print("Script execution took ${time / 1000.0} seconds.")
        printStatistics(proof)
        return if (proof.closed()) ProofState.Success else ProofState.Failed
    }

    private fun loadProof(keyFile: File): ProofState {
        var env: KeYEnvironment<*>? = null
        try {
            env = KeYEnvironment.load(keyFile)
            val proof = env?.loadedProof
            if (proof == null) {
                logger.error("No proof found in given KeY-file.")
                return ProofState.Failed
            }

            if (!proof.closed()) {
                val open = proof.openGoals().size();
                logger.info("Proof has ${proof.openGoals().size()} open goals, running try close macro")
                val pc = env.proofControl;
                proof.openGoals().forEach {
                    pc.runMacro(it.node(), TryCloseMacro(autoModeStep), null)
                    var elapsedMillis = 0;
                    while (pc.isInAutoMode) {
                        try {
                            Thread.sleep(100)
                            elapsedMillis += 100
                        } catch (ignored: InterruptedException) {}
                        if (elapsedMillis == 60000) {
                            logger.info("Failed to close goal ${it.node().serialNr()}")
                            pc.stopAndWaitAutoMode()
                            break
                        }
                    }
                }
                val delta = open - proof.openGoals().size()
                logger.info("Closed $delta goals")
                if (delta > 0) {
                    logger.info("Saving proof")
                    try {
                        proof.saveToFile(keyFile)
                    } catch(e: IOException) {
                        logger.warn("Failed to load proof ", e)
                    }
                }
            }

            try {
                printStatistics(proof)
            }  catch (e: Exception) {
                logger.error("Failed to find statistics")
                e.printStackTrace()
            }

            return if (proof.closed()) ProofState.Success else ProofState.Failed
        } catch (e: Exception) {
            logger.error("Failed load proof ", e)
            return ProofState.Failed
        } finally {
            env?.dispose()
        }
    }


    private fun printStatistics(proof: Proof) {
        if (statisticsFile != null) {
            statistics[proof.name().toString()] = generateSummary(proof)
        }
        if (verbose) {
            proof.statistics.summary.forEach { p -> logger.info("${p.first} = ${p.second}") }
        }
        if (enableMeasuring) {
            val closedGoals = proof.getClosedSubtreeGoals(proof.root())
            val visitLineOnClosedGoals = HashSet<Pair<String, Int>>()
            closedGoals.forEach {
                it.pathToRoot.forEach {
                    val p = it.nodeInfo.activeStatement?.positionInfo
                    if (p != null) {
                        visitLineOnClosedGoals.add(p.fileName to p.startPosition.line)
                    }
                }
            }
            logger.info("Visited lines:\n${visitLineOnClosedGoals.joinToString("\n")}")
        }
    }

    val proofFileCandidates: List<File> by lazy {
        proofPath.asSequence()
            .flatMap { File(it).walkTopDown().asSequence() }
            .filter { it.isFile }
            .filter { it.name.endsWith(".proof") || it.name.endsWith(".proof.gz") }
            .toList()
            .sorted()
    }

    val contractNameToProofFile by lazy {
        if (readContractNames) {
            proofFileCandidates.associateBy { extractContractName(it) }
        } else {
            hashMapOf()
        }
    }


    private fun findProofFile(contractName: String): File? =
        if (contractName in contractNameToProofFile) {
            contractNameToProofFile[contractName]
        } else {
            val filename = MiscTools.toValidFileName(contractName)
            proofFileCandidates.find {
                val name = it.name
                name.startsWith(filename) && (name.endsWith(".proof") || name.endsWith(".proof.gz"))
            }
        }


    private fun findScriptFile(filename: String): File? =
        proofFileCandidates.find {
            val name = it.name
            name.startsWith(filename) && (name.endsWith(".txt") || name.endsWith(".pscript"))
        }
}

fun main(args: Array<String>) = Checker().main(args)

private val Goal.pathToRoot: Sequence<Node>
    get() {
        return generateSequence(node()) { it.parent() }
    }

private fun Proof.openClosedProgramBranches(): Pair<Int, Int> {
    val branchingNodes = this.root().subtreeIterator().asSequence()
        .filter { it.childrenCount() > 1 }
    val programBranchingNodes = branchingNodes.filter {
        val childStmt = it.childrenIterator().asSequence().map { child ->
            child.nodeInfo.activeStatement
        }
        childStmt.any { c -> c != it.nodeInfo.activeStatement }
    }

    val diverseProgramBranches = programBranchingNodes.filter { parent ->
        !parent.isClosed && parent.childrenIterator().asSequence().any { it.isClosed }
    }

    return diverseProgramBranches.count() to programBranchingNodes.count()
}

/**
 * Copied from KeY, but provide a better map
 */
private fun generateSummary(proof: Proof): HashMap<String, Any> {
    val result = HashMap<String, Any>()
    val stat: Statistics = proof.statistics
    result["Nodes"] = stat.nodes
    result["Branches"] = stat.branches
    result["Interactive steps"] = stat.interactiveSteps
    result["Symbolic execution steps"] = stat.symbExApps
    result["Automode time"] = proof.autoModeTime
    result["Avg. time per step"] = stat.timePerStepInMillis
    result["Quantifier instantiations"] = stat.quantifierInstantiations
    result["One-step Simplifier apps"] = stat.ossApps
    result["SMT solver apps"] = stat.smtSolverApps
    result["Dependency Contract apps"] = stat.dependencyContractApps
    result["Operation Contract apps"] = stat.operationContractApps
    result["Block/Loop Contract apps"] = stat.blockLoopContractApps
    result["Loop invariant apps"] = stat.loopInvApps
    result["Merge Rule apps"] = stat.mergeRuleApps
    result["Total rule apps"] = stat.totalRuleApps
    result["Interactive Rule Apps"] = stat.interactiveAppsDetails
    return result
}

private fun extractContractName(it: File): String? {
    val input = if (it.name.endsWith(".gz")) {
        GZIPInputStream(FileInputStream(it))
    } else {
        FileInputStream(it)
    }
    input.bufferedReader().use { incoming ->
        val contractLine = incoming.lineSequence().find { it.startsWith("name=") }
        return contractLine?.trim()?.substring("name=".length)
    }
}


enum class ProofState {
    Success, Failed, Skipped
}

internal fun obj2json(any: Any?): String =
    when (any) {
        null -> "null"
        is String -> "\"$any\""
        is Long, Int, Float, Double -> any.toString()
        is Map<*, *> -> "{${any.entries.joinToString(",\n") { (k, v) -> "\"$k\" : ${obj2json(v)}" }}}"
        is List<*> -> "[${any.joinToString(",") { obj2json(it) }}]"
        else -> any.toString()
    }

//region Measuring
class MeasuringMacro : SequentialProofMacro() {
    val before = Stats()
    val after = Stats()

    override fun getName() = "MeasuringMacro"
    override fun getCategory() = "ci-only"
    override fun getDescription() = "like auto but with more swag"

    override fun createProofMacroArray(): Array<ProofMacro> {
        return arrayOf(
            AutoPilotPrepareProofMacro(),
            GatherStatistics(before),
            AutoMacro(), //or TryCloseMacro()?
            GatherStatistics(after)
        )
    }
}

data class Stats(var openGoals: Int = 0, var closedGoals: Int = 0)

class GatherStatistics(val stats: Stats) : SkipMacro() {
    override fun getName() = "gather-stats"
    override fun getCategory() = "ci-only"
    override fun getDescription() = "stat purpose"

    override fun canApplyTo(
        proof: Proof?,
        goals: ImmutableList<Goal?>?,
        posInOcc: PosInOccurrence?
    ): Boolean = true

    override fun applyTo(
        uic: UserInterfaceControl?,
        proof: Proof,
        goals: ImmutableList<Goal?>?,
        posInOcc: PosInOccurrence?,
        listener: ProverTaskListener?
    ): ProofMacroFinishedInfo? { // do nothing
        stats.openGoals = proof.openGoals().size()
        stats.closedGoals = proof.getClosedSubtreeGoals(proof.root()).size()
        return super.applyTo(uic, proof, goals, posInOcc, listener)
    }
}
//endregion