"""Consolidation controls for the current flat, one-library-per-module project.

Use Lean's dependency output, not a source import parser. This verifies module
reachability, not theorem namespace policy or the soundness of Lean itself.
"""
import pathlib
import subprocess
import tomllib
import unittest

PROJECT = pathlib.Path(__file__).resolve().parents[1]
EXECUTABLE_CLIENTS = {"hardware/Main.lean", "experiments/accuracy_search/Main.lean", "experiments/key_two_corner/Main.lean"}
SEMANTIC_FIXTURES = {
    "RedundantCF.lean": "GeneralizedIntervalArithmetic.RedundantCFChecks",
    "InfiniteSimpleCF.lean": "GeneralizedIntervalArithmetic.InfiniteSimpleCFChecks",
    "DigitExtraction.lean": "GeneralizedIntervalArithmetic.DigitExtractionChecks",
    "MonotoneUnions.lean": "GeneralizedIntervalArithmetic.MonotoneUnionsChecks",
    "FractionalProjection.lean": "GeneralizedIntervalArithmetic.FractionalProjectionChecks",
    "RationalFamilyClosure.lean": "GeneralizedIntervalArithmetic.RationalFamilyClosureChecks",
    "NearestMinimizers.lean": "GeneralizedIntervalArithmetic.NearestMinimizersChecks",
    "SourceRoundedAlgebra.lean": "GeneralizedIntervalArithmetic.SourceRoundedAlgebraChecks",
    "DirectedOperationAlgebra.lean": "GeneralizedIntervalArithmetic.DirectedOperationAlgebraChecks",
    "NumericFoundations.lean": "GeneralizedIntervalArithmetic.NumericFoundationsChecks",
    "UnboundedPieceComposition.lean": "GeneralizedIntervalArithmetic.UnboundedPieceCompositionChecks",
    "AffinePoleSplit.lean": "GeneralizedIntervalArithmetic.AffinePoleSplitChecks",
    "GuardedPieceComposition.lean": "GeneralizedIntervalArithmetic.GuardedPieceCompositionChecks",
    "PieceDomainConversion.lean": "GeneralizedIntervalArithmetic.PieceDomainConversionChecks",
    "PartialImageTransfer.lean": "GeneralizedIntervalArithmetic.PartialImageTransferChecks",
    "RootTransfer.lean": "GeneralizedIntervalArithmetic.RootTransferChecks",
    "InfiniteAdditionTransfer.lean": "GeneralizedIntervalArithmetic.InfiniteAdditionTransferChecks",
    "FormatNormalization.lean": "GeneralizedIntervalArithmetic.FormatNormalizationChecks",
    "HansenRealSets.lean": "GeneralizedIntervalArithmetic.HansenRealSetsChecks",
    "HansenCoefficients.lean": "GeneralizedIntervalArithmetic.HansenCoefficientsChecks",
    "MixedEndpoints.lean": "GeneralizedIntervalArithmetic.MixedEndpointsChecks",
    "CoefficientWitnesses.lean": "GeneralizedIntervalArithmetic.CoefficientWitnessesChecks",
    "FiniteGuardPieces.lean": "GeneralizedIntervalArithmetic.FiniteGuardPiecesChecks",
    "EndpointOptimality.lean": "GeneralizedIntervalArithmetic.EndpointOptimalityChecks",
    "Binary64Format.lean": "GeneralizedIntervalArithmetic.Binary64FormatChecks",
    "FormatDigits.lean": "GeneralizedIntervalArithmetic.FormatDigitsChecks",
    "FiniteFormat.lean": "GeneralizedIntervalArithmetic.FiniteFormatChecks",
    "TaggedConversion.lean": "GeneralizedIntervalArithmetic.TaggedConversionChecks",
    "DescriptorDemotion.lean": "GeneralizedIntervalArithmetic.DescriptorDemotionChecks",
    "ContinuedFractionConversion.lean": "GeneralizedIntervalArithmetic.ContinuedFractionConversionChecks",
    "ExceptionalFamilies.lean": "GeneralizedIntervalArithmetic.ExceptionalFamiliesChecks",
    "FiniteFamilyChain.lean": "GeneralizedIntervalArithmetic.FiniteFamilyChainChecks",
    "SequenceRepresentations.lean": "GeneralizedIntervalArithmetic.SequenceRepresentationsChecks",
    "DigitRepresentations.lean": "GeneralizedIntervalArithmetic.DigitRepresentationsChecks",
    "CutArithmetic.lean": "GeneralizedIntervalArithmetic.CutArithmeticChecks",
    "DedekindBoundary.lean": "GeneralizedIntervalArithmetic.DedekindBoundaryChecks",
    "FinitePointDescriptions.lean": "GeneralizedIntervalArithmetic.FinitePointDescriptionsChecks",
    "IntervalSetExtension.lean": "GeneralizedIntervalArithmetic.IntervalSetExtensionChecks",
    "QuadraticFamilies.lean": "GeneralizedIntervalArithmetic.QuadraticFamiliesChecks",
    "MultiAffineFamilies.lean": "GeneralizedIntervalArithmetic.MultiAffineFamiliesChecks",
    "LinearFamilyEquality.lean": "GeneralizedIntervalArithmetic.LinearFamilyEqualityChecks",
    "TrackingCertificates.lean": "GeneralizedIntervalArithmetic.TrackingCertificatesChecks",
    "InfinityStreams.lean": "GeneralizedIntervalArithmetic.InfinityStreamsChecks",
    "DiscreteDemotion.lean": "GeneralizedIntervalArithmetic.DiscreteDemotionChecks",
    "IntervalAlgebra.lean": "GeneralizedIntervalArithmetic.IntervalAlgebraChecks",
    "AccuracySearchExample.lean": "GeneralizedIntervalArithmetic.AccuracySearchExampleChecks",
    "ExpressionStreams.lean": "GeneralizedIntervalArithmetic.ExpressionStreamsChecks",
    "ReciprocalStreams.lean": "GeneralizedIntervalArithmetic.ReciprocalStreamsChecks",
    "AffineDemotionLimits.lean": "GeneralizedIntervalArithmetic.AffineDemotionLimitsChecks",
    "IntervalCoefficientVariants.lean": "GeneralizedIntervalArithmetic.IntervalCoefficientVariantsChecks",
    "IntervalSetDenotation.lean": "GeneralizedIntervalArithmetic.IntervalSetDenotationChecks",
    "NumberPromotion.lean": "GeneralizedIntervalArithmetic.NumberPromotionChecks",
    "FiniteProperties.lean": "GeneralizedIntervalArithmetic.FinitePropertiesChecks",
    "PartialProperties.lean": "GeneralizedIntervalArithmetic.PartialPropertiesChecks",
    "GeneralFamilyDemotion.lean": "GeneralizedIntervalArithmetic.GeneralFamilyDemotionChecks",
    "FamilyDemotion.lean": "GeneralizedIntervalArithmetic.FamilyDemotionChecks",
    "ExceptionalComparisons.lean": "GeneralizedIntervalArithmetic.ExceptionalComparisonsChecks",
    "ExtendedImageHull.lean": "GeneralizedIntervalArithmetic.ExtendedImageHullChecks",
    "HyperrealInfinitesimal.lean": "GeneralizedIntervalArithmetic.HyperrealInfinitesimalChecks",
    "FiniteEquality.lean": "GeneralizedIntervalArithmetic.FiniteEqualityChecks",
    "DomainProjections.lean": "GeneralizedIntervalArithmetic.DomainProjectionsChecks",
    "DomainConstraints.lean": "GeneralizedIntervalArithmetic.DomainConstraintsChecks",
    "BooleanComposition.lean": "GeneralizedIntervalArithmetic.BooleanCompositionChecks",
    "StrictComparison.lean": "GeneralizedIntervalArithmetic.StrictComparisonChecks",

    "ExactImageHull.lean": "GeneralizedIntervalArithmetic.ExactImageHullChecks",
    "KeyTwoCorner.lean": "GeneralizedIntervalArithmetic.KeyTwoCornerChecks",
    "Binary64Key.lean": "GeneralizedIntervalArithmetic.Binary64KeyChecks",
    "WordTwoCorner.lean": "GeneralizedIntervalArithmetic.WordTwoCornerChecks",
    "TwoCornerRefinement.lean": "GeneralizedIntervalArithmetic.TwoCornerRefinementChecks",
    "FiniteAffineDemotion.lean": "GeneralizedIntervalArithmetic.FiniteAffineDemotionChecks",
    "AffineConjunction.lean": "GeneralizedIntervalArithmetic.AffineConjunctionChecks",
    "TwoCornerDivision.lean": "GeneralizedIntervalArithmetic.TwoCornerDivisionChecks",
    "SplitQuotient.lean": "GeneralizedIntervalArithmetic.SplitQuotientChecks",
    "ResidueInference.lean": "GeneralizedIntervalArithmetic.ResidueInferenceChecks",
    "IntegerResidue.lean": "GeneralizedIntervalArithmetic.IntegerResidueChecks",
    "DirectedScheduling.lean": "GeneralizedIntervalArithmetic.DirectedSchedulingChecks",
    "PartialRealArithmetic.lean": "GeneralizedIntervalArithmetic.PartialRealArithmeticChecks",
    "Binary64.lean": "GeneralizedIntervalArithmetic.Binary64Checks",
    "AffineUnary.lean": "GeneralizedIntervalArithmetic.AffineUnaryChecks",
    "TangentBounds.lean": "GeneralizedIntervalArithmetic.TangentChecks",
    "EndpointChords.lean": "GeneralizedIntervalArithmetic.EndpointChordChecks",
    "HardwareQuotient.lean": "GeneralizedIntervalArithmetic.HardwareQuotientChecks",
    "HardwareEvaluator.lean": "GeneralizedIntervalArithmetic.HardwareEvaluatorChecks",
    "HardwareAffineProduct.lean": "GeneralizedIntervalArithmetic.HardwareAffineProductChecks",
    "HardwareAffine.lean": "GeneralizedIntervalArithmetic.HardwareAffineChecks",
    "TrigHalving.lean": "GeneralizedIntervalArithmetic.TrigHalvingChecks",
    "SplitReduction.lean": "GeneralizedIntervalArithmetic.SplitReductionChecks",
    "DyadicReduction.lean": "GeneralizedIntervalArithmetic.DyadicReductionChecks",
    "CosineQuadrants.lean": "GeneralizedIntervalArithmetic.CosineQuadrantChecks",
    "SineReduction.lean": "GeneralizedIntervalArithmetic.SineReductionChecks",
    "SineEndpoints.lean": "GeneralizedIntervalArithmetic.SineEndpointChecks",
    "HardwareSine.lean": "GeneralizedIntervalArithmetic.HardwareSineChecks",
    "HardwareSquareRoot.lean": "GeneralizedIntervalArithmetic.HardwareSquareRootChecks",
    "HardwareDivision.lean": "GeneralizedIntervalArithmetic.HardwareDivisionChecks",
    "HardwareMultiplication.lean": "GeneralizedIntervalArithmetic.HardwareMultiplicationChecks",
    "HardwareSubtraction.lean": "GeneralizedIntervalArithmetic.HardwareSubtractionChecks",
    "HardwareAddition.lean": "GeneralizedIntervalArithmetic.HardwareAdditionChecks",
    "MonotoneIntegerBounds.lean": "GeneralizedIntervalArithmetic.IntegerBoundChecks",
    "BasicIntervalOps.lean": "GeneralizedIntervalArithmetic.BasicOperationChecks",
    "NonzeroDomains.lean": "GeneralizedIntervalArithmetic.NonzeroDomainChecks",
    "PropertyComposition.lean": "GeneralizedIntervalArithmetic.PropertyCompositionChecks",
    "SquareRootDomains.lean": "GeneralizedIntervalArithmetic.SquareRootChecks",
    "UniversalDomains.lean": "GeneralizedIntervalArithmetic.UniversalDomainChecks",
    "TwoParameterBounds.lean": "GeneralizedIntervalArithmetic.TwoParameterChecks",
    "QuadraticChord.lean": "GeneralizedIntervalArithmetic.QuadraticChordChecks",
    "ConstantEmbedding.lean": "GeneralizedIntervalArithmetic.ConstantEmbeddingChecks",
    "AffineCorrespondence.lean": "GeneralizedIntervalArithmetic.AffineCorrespondenceChecks",
    "DomainSearchIntegration.lean": "GeneralizedIntervalArithmetic.DomainSearchIntegrationChecks",
    "AffineRegionSubdivision.lean": "GeneralizedIntervalArithmetic.AffineRegionSubdivisionChecks",
    "AffineRegionSearch.lean": "GeneralizedIntervalArithmetic.AffineRegionSearchChecks",
    "AffineRegions.lean": "GeneralizedIntervalArithmetic.AffineRegionChecks",
    "AffineSegmentDomains.lean": "GeneralizedIntervalArithmetic.AffineSegmentChecks",
    "AffineDomainGuards.lean": "GeneralizedIntervalArithmetic.AffineGuardChecks",
    "OptionalRangePrototype.lean": "GeneralizedIntervalArithmetic.OptionalRangePrototype",
    "UncertainDomains.lean": "GeneralizedIntervalArithmetic.UncertainDomainChecks",
    "PointDomains.lean": "GeneralizedIntervalArithmetic.PointDomainChecks",
    "QuotientDomains.lean": "GeneralizedIntervalArithmetic.QuotientDomainChecks",
    "DomainQueries.lean": "GeneralizedIntervalArithmetic.DomainQueryChecks",
    "ThresholdCertificates.lean": "GeneralizedIntervalArithmetic.ThresholdCertificateChecks",
    "Integration.lean": "GeneralizedIntervalArithmetic.IntegrationChecks",
    "CoverPipeline.lean": "GeneralizedIntervalArithmetic.CoverPipelineChecks",
    "CellCertificates.lean": "GeneralizedIntervalArithmetic.CellCertificateChecks",
}


def reachable(graph, roots):
    seen = set()
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph[module])
    return seen


def coverage_errors(modules, libraries, defaults, graph):
    errors = []
    if modules != libraries:
        errors.append("source/library inventory mismatch")
    if "Audit" not in defaults:
        errors.append("Audit is not a default target")
    if modules - reachable(graph, ["Audit"]):
        errors.append("modules outside audit import closure")
    if modules - reachable(graph, defaults):
        errors.append("modules outside default build closure")
    return errors


class ProjectIntegrationTests(unittest.TestCase):
    def test_all_modules_registered_built_and_imported_by_audit(self):
        modules = {p.stem for p in PROJECT.glob("*.lean")}
        nested = [p.relative_to(PROJECT) for p in PROJECT.rglob("*.lean")
                  if p.parent != PROJECT and p.relative_to(PROJECT).parts[0] not in {".lake", "tests"}]
        self.assertEqual({str(p) for p in nested}, EXECUTABLE_CLIENTS,
                         "Register executable clients explicitly; proof libraries remain flat")
        config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
        libraries = {lib["name"] for lib in config["lean_lib"]}
        self.assertEqual(modules, libraries)
        graph = {}
        artifacts = (PROJECT / ".lake/build/lib/lean").resolve()
        for module in sorted(modules):
            result = subprocess.run(
                ["lake", "env", "lean", "--deps", f"{module}.lean"],
                cwd=PROJECT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=60, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            paths = [(PROJECT / line).resolve() for line in result.stdout.splitlines() if line]
            graph[module] = {p.stem for p in paths if p.parent == artifacts}
            self.assertTrue(graph[module] <= modules, graph[module] - modules)
        self.assertEqual(coverage_errors(modules, libraries, config["defaultTargets"], graph), [])
        # Keep independent clients independent even through transitive imports.
        for fixture in SEMANTIC_FIXTURES:
            result = subprocess.run(
                ["lake", "env", "lean", "--deps", f"tests/{fixture}"],
                cwd=PROJECT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=60, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            paths = [(PROJECT / line).resolve() for line in result.stdout.splitlines() if line]
            roots = {p.stem for p in paths if p.parent == artifacts}
            example_dependencies = {name for name in reachable(graph, roots)
                                    if name.endswith("Examples")}
            self.assertEqual(example_dependencies, set(), fixture)

    def test_semantic_fixture_inventory(self):
        fixtures = {str(p.relative_to(PROJECT / "tests"))
                    for p in (PROJECT / "tests").rglob("*.lean")}
        self.assertEqual(fixtures, set(SEMANTIC_FIXTURES),
                         "Register each persistent Lean fixture for a fresh process and audit")

    def test_omitted_module_is_detected(self):
        graph = {"Audit": {"Core"}, "Core": set(), "Forgotten": set()}
        self.assertIn("modules outside audit import closure",
                      coverage_errors(set(graph), set(graph), ["Audit", "Forgotten"], graph))

    def test_removed_default_audit_is_detected(self):
        graph = {"Audit": {"Core"}, "Core": set()}
        self.assertIn("Audit is not a default target",
                      coverage_errors(set(graph), set(graph), ["Core"], graph))

    def test_unregistered_source_is_detected(self):
        graph = {"Audit": {"Core"}, "Core": set()}
        self.assertIn("source/library inventory mismatch",
                      coverage_errors(set(graph), {"Audit"}, ["Audit"], graph))

    def test_fresh_end_to_end_semantics(self):
        for fixture, namespace in SEMANTIC_FIXTURES.items():
            with self.subTest(fixture=fixture):
                result = subprocess.run(
                    ["lake", "env", "lean", f"tests/{fixture}"], cwd=PROJECT,
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    timeout=120, check=False,
                )
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertIn(f"axiom audit passed namespace {namespace}:", result.stdout)
                self.assertNotIn("warning:", result.stdout)


if __name__ == "__main__":
    unittest.main()
