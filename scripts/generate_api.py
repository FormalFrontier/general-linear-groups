#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
# Original ideal-completion adapter: Anchor (AI).
# Group and Dedekind portability, GLG inventory, module ownership, assumptions,
# tests and documentation adapted by Prism (AI); Beacon (AI) advised on portability.
"""Generate this library's Markdown API from pinned native doc-gen4 records.

This is a deliberately 128-declaration adapter, not a general documentation
certifier, a Lean parser, or a proof check. Native generation receipts remain
separate review evidence. See docs/README.md for the reproduction contract.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
MODULE_PATHS = {
    "GeneralLinearGroups": "GeneralLinearGroups.lean",
    "GeneralLinearGroups.AdditiveCommutator": "GeneralLinearGroups/AdditiveCommutator.lean",
    "GeneralLinearGroups.CongruenceSubgroup": "GeneralLinearGroups/CongruenceSubgroup.lean",
    "GeneralLinearGroups.LocalQuotient": "GeneralLinearGroups/LocalQuotient.lean",
    "GeneralLinearGroups.MatrixQuasiregular": "GeneralLinearGroups/MatrixQuasiregular.lean",
    "GeneralLinearGroups.MatrixTrace": "GeneralLinearGroups/MatrixTrace.lean",
    "GeneralLinearGroups.NilIdeal": "GeneralLinearGroups/NilIdeal.lean",
    "GeneralLinearGroups.NonUnitalNilpotent": "GeneralLinearGroups/NonUnitalNilpotent.lean",
    "GeneralLinearGroups.NonUnitalQuasiregular": "GeneralLinearGroups/NonUnitalQuasiregular.lean",
    "GeneralLinearGroups.QuasiregularIdeal": "GeneralLinearGroups/QuasiregularIdeal.lean",
    "GeneralLinearGroups.QuasiregularQuotient": "GeneralLinearGroups/QuasiregularQuotient.lean",
    "GeneralLinearGroups.Reindex": "GeneralLinearGroups/Reindex.lean",
    "GeneralLinearGroups.UnitalComparison": "GeneralLinearGroups/UnitalComparison.lean",
    "GeneralLinearGroups.Whitehead": "GeneralLinearGroups/Whitehead.lean",
    "MatrixTraceClient": "tests/MatrixTraceClient.lean",
    "PublicAPIClient": "tests/PublicAPIClient.lean"
}
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values()) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
# Explicit author-time native inventory, checked against the actual source statements.
# Each row: module, native kind, displayed kind, all implicit binders/typeclasses.
# Root and private-client modules deliberately contribute no public entries.
INVENTORY = {
    "Ring.additiveCommutators": [
        "GeneralLinearGroups.AdditiveCommutator",
        "def",
        "def",
        [
            "[Ring R]"
        ]
    ],
    "Ring.commutator_mem_additiveCommutators": [
        "GeneralLinearGroups.AdditiveCommutator",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealInclusion": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "[ℤ]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealUnitizationToRing": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealUnitizationToRing_apply": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealAugmentation": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroup": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.congruenceSubgroup": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealUnitizationMap": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.quotient_mk_ideal_coe_eq_zero": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroup_map_mem_congruenceSubgroup": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToCongruence": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroup_entry_fst": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.congruenceSubgroup_entry_sub_mem": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.liftCongruenceEntry": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.liftCongruenceMatrix": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.liftCongruenceEntry_fst": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealUnitizationToRing_liftCongruenceEntry": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.fstHom_map_liftCongruenceMatrix": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealUnitizationToRing_map_liftCongruenceMatrix": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitization_eq_of_fst_eq_of_idealUnitizationToRing_eq": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{x y : Unitization ℤ ↥I}"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]",
            "{x y : Matrix n n (Unitization ℤ ↥I)}"
        ]
    ],
    "Matrix.GeneralLinearGroup.liftCongruenceUnit": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.congruenceSubgroupToIdealGeneralLinearGroup": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToCongruence_rightInverse": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToCongruence_injective": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToCongruence_bijective": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupEquivCongruence": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "noncomputable def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToRing": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToRing_injective": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToRing_mulExact": [
        "GeneralLinearGroups.CongruenceSubgroup",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "TwoSidedIdeal.isMaximal_asIdeal_of_isUnit_compl": [
        "GeneralLinearGroups.LocalQuotient",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.quotientDivisionRing": [
        "GeneralLinearGroups.LocalQuotient",
        "def",
        "noncomputable abbrev",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.IsQuasiregular.matrix": [
        "GeneralLinearGroups.MatrixQuasiregular",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I : TwoSidedIdeal R}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.trace_mul_sub_trace_mul_commutators": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{m : Type uM}",
            "{n : Type uN}",
            "[Fintype m]",
            "[Fintype n]"
        ]
    ],
    "Matrix.trace_mul_sub_trace_mul_mem_additiveCommutators": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{m : Type uM}",
            "{n : Type uN}",
            "[Fintype m]",
            "[Fintype n]"
        ]
    ],
    "Matrix.additiveCommutators_le_trace_comap": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.traceOnCommutatorQuotient": [
        "GeneralLinearGroups.MatrixTrace",
        "def",
        "def",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.traceOnCommutatorQuotient_mk": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.additiveCommutators_le_corner_comap": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.offDiagonal_single_mem_additiveCommutators": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.diagonal_single_sub_corner_mem_additiveCommutators": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.single_sub_corner_trace_mem_additiveCommutators": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.sub_corner_trace_mem_additiveCommutators": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.mem_additiveCommutators_iff_trace_mem": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.cornerOnCommutatorQuotient": [
        "GeneralLinearGroups.MatrixTrace",
        "def",
        "def",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.cornerOnCommutatorQuotient_mk": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.corner_traceOnCommutatorQuotient": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.traceOnCommutatorQuotient_corner": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.traceQuotientEquiv": [
        "GeneralLinearGroups.MatrixTrace",
        "def",
        "def",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.traceQuotientEquiv_mk": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.traceQuotientEquiv_symm_mk": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.cornerOnCommutatorQuotient_independent": [
        "GeneralLinearGroups.MatrixTrace",
        "theorem",
        "theorem",
        [
            "{R : Type uR}",
            "[Ring R]",
            "{n : Type uN}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "TwoSidedIdeal.IsNil": [
        "GeneralLinearGroups.NilIdeal",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.IsNil.mono": [
        "GeneralLinearGroups.NilIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I J : TwoSidedIdeal R}"
        ]
    ],
    "TwoSidedIdeal.isNil_bot": [
        "GeneralLinearGroups.NilIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.IsNil.isQuasiregular": [
        "GeneralLinearGroups.NilIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I : TwoSidedIdeal R}"
        ]
    ],
    "TwoSidedIdeal.IsNil.le_ringJacobson": [
        "GeneralLinearGroups.NilIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I : TwoSidedIdeal R}"
        ]
    ],
    "NonUnital.positivePow": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{A : Type u}",
            "[Mul A]"
        ]
    ],
    "NonUnital.positivePow_zero": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{A : Type u}",
            "[Mul A]"
        ]
    ],
    "NonUnital.positivePow_succ": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{A : Type u}",
            "[Mul A]"
        ]
    ],
    "NonUnital.IsNilpotent": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{A : Type u}",
            "[SemigroupWithZero A]"
        ]
    ],
    "IsNilpotent.oneAddUnitOfPowEqZero": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{A : Type u_1}",
            "[Ring A]"
        ]
    ],
    "IsNilpotent.oneAddUnitOfPowEqZero_val": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{A : Type u_1}",
            "[Ring A]"
        ]
    ],
    "IsNilpotent.oneAddUnitOfPowEqZero_inv": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{A : Type u_1}",
            "[Ring A]"
        ]
    ],
    "Matrix.IsStrictlyUpperTriangular": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : ℕ}"
        ]
    ],
    "Matrix.positivePow_apply_eq_zero_of_isStrictlyUpperTriangular": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : ℕ}",
            "{x : Matrix (Fin n) (Fin n) I}"
        ]
    ],
    "Matrix.IsStrictlyUpperTriangular.isNilpotent": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : ℕ}",
            "{x : Matrix (Fin n) (Fin n) I}"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationMatrix": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{I : Type u}",
            "{n : Type v}"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationMatrix_zero": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationMatrix_mul": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationMatrix_positivePow": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.isNilpotent_unitizationMatrix": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalAugmentation": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalGeneralLinearGroup": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nilpotentMatrixElement": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "def",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nilpotentMatrixElement_val": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nilpotentMatrixElement_inv": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalGeneralLinearGroupOfIsNilpotent": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "def",
        "noncomputable def",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalGeneralLinearGroupOfIsNilpotent_val": [
        "GeneralLinearGroups.NonUnitalNilpotent",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.isUnit_one_add_unitizationMatrix_iff_isQuasiregular": [
        "GeneralLinearGroups.NonUnitalQuasiregular",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.exists_nonUnitalGeneralLinearGroup_iff_isQuasiregular": [
        "GeneralLinearGroups.NonUnitalQuasiregular",
        "theorem",
        "theorem",
        [
            "{I : Type u}",
            "[NonUnitalRing I]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "TwoSidedIdeal.IsQuasiregular": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.IsRightQuasiregular": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "def",
        "def",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.exists_rightQuasiInverse_mem_of_isUnit_one_add": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{x : R}"
        ]
    ],
    "TwoSidedIdeal.exists_quasiInverse_mem_of_isRightQuasiregular": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I : TwoSidedIdeal R}",
            "{x : R}"
        ]
    ],
    "TwoSidedIdeal.isQuasiregular_iff_isRightQuasiregular": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.isRightQuasiregular_iff_forall_isUnit_one_add": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.ringJacobson_isQuasiregular": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]"
        ]
    ],
    "TwoSidedIdeal.IsQuasiregular.le_ringJacobson": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I : TwoSidedIdeal R}"
        ]
    ],
    "TwoSidedIdeal.ringJacobson_isGreatest_isQuasiregular": [
        "GeneralLinearGroups.QuasiregularIdeal",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{I : TwoSidedIdeal R | I.IsQuasiregular}"
        ]
    ],
    "Matrix.GeneralLinearGroup.isUnit_of_mapMatrix_quotient_isUnit": [
        "GeneralLinearGroups.QuasiregularQuotient",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_quotient_surjective": [
        "GeneralLinearGroups.QuasiregularQuotient",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.idealGeneralLinearGroupToRing_shortExact": [
        "GeneralLinearGroups.QuasiregularQuotient",
        "theorem",
        "theorem",
        [
            "{R : Type u}",
            "[Ring R]",
            "{n : Type v}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.reindexEquiv": [
        "GeneralLinearGroups.Reindex",
        "def",
        "def",
        [
            "{ι : Type uι}",
            "{κ : Type uκ}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Fintype κ]",
            "[DecidableEq κ]",
            "[Semiring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.reindexEquiv_apply": [
        "GeneralLinearGroups.Reindex",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "{κ : Type uκ}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Fintype κ]",
            "[DecidableEq κ]",
            "[Semiring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.reindexEquiv_symm_apply": [
        "GeneralLinearGroups.Reindex",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "{κ : Type uκ}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Fintype κ]",
            "[DecidableEq κ]",
            "[Semiring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.reindexEquiv_symm": [
        "GeneralLinearGroups.Reindex",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "{κ : Type uκ}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Fintype κ]",
            "[DecidableEq κ]",
            "[Semiring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.reindexEquiv_refl": [
        "GeneralLinearGroups.Reindex",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Semiring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.reindexEquiv_trans": [
        "GeneralLinearGroups.Reindex",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "{κ : Type uκ}",
            "{τ : Type uτ}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Fintype κ]",
            "[DecidableEq κ]",
            "[Semiring R]",
            "[Fintype τ]",
            "[DecidableEq τ]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_reindexEquiv": [
        "GeneralLinearGroups.Reindex",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "{κ : Type uκ}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "[Fintype κ]",
            "[DecidableEq κ]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Semiring R]",
            "[Semiring S]"
        ]
    ],
    "Unitization.ringEquivProd": [
        "GeneralLinearGroups.UnitalComparison",
        "def",
        "def",
        [
            "[CommRing R]",
            "[Ring A]",
            "[Algebra R A]"
        ]
    ],
    "Unitization.ringEquivProd_apply": [
        "GeneralLinearGroups.UnitalComparison",
        "theorem",
        "theorem",
        [
            "[CommRing R]",
            "[Ring A]",
            "[Algebra R A]"
        ]
    ],
    "Unitization.ringEquivProd_symm_apply": [
        "GeneralLinearGroups.UnitalComparison",
        "theorem",
        "theorem",
        [
            "[CommRing R]",
            "[Ring A]",
            "[Algebra R A]"
        ]
    ],
    "Matrix.GeneralLinearGroup.matrixRingEquivProd": [
        "GeneralLinearGroups.UnitalComparison",
        "def",
        "def",
        [
            "[CommRing R]",
            "[Ring A]",
            "{n : Type w}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationGeneralLinearEquivProd": [
        "GeneralLinearGroups.UnitalComparison",
        "def",
        "def",
        [
            "[CommRing R]",
            "[Ring A]",
            "[Algebra R A]",
            "{n : Type w}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.unitizationGeneralLinearEquivProd_fst": [
        "GeneralLinearGroups.UnitalComparison",
        "theorem",
        "theorem",
        [
            "[CommRing R]",
            "[Ring A]",
            "[Algebra R A]",
            "{n : Type w}",
            "[Fintype n]",
            "[DecidableEq n]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalGeneralLinearGroupEquiv": [
        "GeneralLinearGroups.UnitalComparison",
        "def",
        "def",
        [
            "{n : Type w}",
            "[Fintype n]",
            "[DecidableEq n]",
            "[Ring I]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalGeneralLinearGroupEquiv_apply": [
        "GeneralLinearGroups.UnitalComparison",
        "theorem",
        "theorem",
        [
            "{n : Type w}",
            "[Fintype n]",
            "[DecidableEq n]",
            "[Ring I]"
        ]
    ],
    "Matrix.GeneralLinearGroup.nonUnitalGeneralLinearGroupEquiv_symm_val": [
        "GeneralLinearGroups.UnitalComparison",
        "theorem",
        "theorem",
        [
            "{n : Type w}",
            "[Fintype n]",
            "[DecidableEq n]",
            "[Ring I]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "def",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Semiring R]",
            "[Semiring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_apply": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Semiring R]",
            "[Semiring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_id": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "[Semiring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_comp": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "{T : Type uT}",
            "[Semiring R]",
            "[Semiring S]",
            "[Semiring T]"
        ]
    ],
    "Matrix.GeneralLinearGroup.BlockMatrix": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "abbrev",
        [
            "{ι : Type uι}",
            "{R : Type uR}"
        ]
    ],
    "Matrix.GeneralLinearGroup.upperUnit": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "def",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.lowerUnit": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "def",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.swapUnit": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "def",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.blockDiagonalUnit": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "def",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.blockDiagonalUnit_eq": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "[Ring R]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_upperUnit": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_lowerUnit": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_swapUnit": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.liftMatrix": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "noncomputable def",
        [
            "{ι : Type uι}",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapMatrix_liftMatrix": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.liftBlockDiagonal": [
        "GeneralLinearGroups.Whitehead",
        "def",
        "noncomputable def",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ],
    "Matrix.GeneralLinearGroup.mapRingHom_liftBlockDiagonal": [
        "GeneralLinearGroups.Whitehead",
        "theorem",
        "theorem",
        [
            "{ι : Type uι}",
            "[Fintype ι]",
            "[DecidableEq ι]",
            "{R : Type uR}",
            "{S : Type uS}",
            "[Ring R]",
            "[Ring S]"
        ]
    ]
}
EXPECTED = {name: row[1] for name, row in INVENTORY.items()}
DECL_MODULES = {name: row[0] for name, row in INVENTORY.items()}


def assumptions(name):
    return tuple(INVENTORY[name][3])


def displayed_kind(name, kind):
    return INVENTORY[name][2]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def load_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object)


def native_hashes(records):
    return {m: digest(json.dumps(records[m], sort_keys=True).encode()) for m in MODULES}


def validate_binding(binding, revision, sources, records):
    """Check retained inputs, not the truth or independent approval of their origin."""
    require(type(revision) is str and re.fullmatch(r"[0-9a-f]{40}", revision) is not None,
            "full source revision required")
    require(type(binding) is dict and set(binding) == {
        "format", "generator", "docgen_revision", "adapter_sha256",
        "analyzed_source_revision", "modules", "inputs", "public_declarations",
        "native_record_sha256", "api_sha256", "proof_certification"},
        "binding fields differ")
    require(type(binding["format"]) is int and binding["format"] == 1,
            "binding format differs")
    require(binding["generator"] == "scripts/generate_api.py" and
            binding["docgen_revision"] == TOOL, "binding generator/tool differs")
    require(binding["analyzed_source_revision"] == revision, "binding revision differs")
    require(binding["modules"] == list(MODULES), "binding module inventory differs")
    require(type(binding["public_declarations"]) is list and
            len(binding["public_declarations"]) == len(EXPECTED) and
            all(type(name) is str for name in binding["public_declarations"]) and
            set(binding["public_declarations"]) == set(EXPECTED),
            "binding public inventory differs")
    require(set(sources) == set(INPUTS) and set(records) == set(MODULES),
            "source/native inventory differs")
    require(binding["inputs"] == {p: digest(sources[p]) for p in sorted(sources)},
            "source/pin drift from retained binding")
    require(binding["native_record_sha256"] == native_hashes(records),
            "native records drift from retained binding")
    require(binding["proof_certification"] is False, "binding claims proof certification")
    for name in ["adapter_sha256", "api_sha256"]:
        require(type(binding[name]) is str and re.fullmatch(r"[0-9a-f]{64}", binding[name]) is not None,
                "malformed binding digest: " + name)
    # A changed adapter may reproduce the same retained inputs. The regenerated
    # manifest binds the new adapter; --check compares that entire output exactly.


class Header(HTMLParser):
    """Keep all visible text, including every implicit argument; discard markup."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(k.startswith("on") for k in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        # Whitespace alone is normalized; all tokens and implicit binders remain.
        return " ".join("".join(self.text).split())


def render(records, revision, sources):
    require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, "full source revision required")
    require(set(records) == set(MODULES), "shipped module records differ")
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    rows = []
    found = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in EXPECTED and EXPECTED[name] == kind, "unexpected public name/kind")
            require(module == DECL_MODULES[name], "unexpected public declaration in module")
            require(name not in found, "duplicate public declaration")
            path = MODULE_PATHS[module]
            prefix = "source-snapshot:" + revision + "/" + path
            # Pinned SourceLinker leaves non-GitHub/non-VSCode identifiers unchanged.
            # No public URL is invented merely to obtain its optional range suffix.
            require(info["sourceLink"] == prefix,
                    "native record is not bound to selected immutable source")
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            require(type(info["line"]) is int and 0 < info["line"] <= len(sources[path].splitlines()),
                    "invalid native source line")
            header = Header(row["header"])
            require("".join(header.names) == name and "".join(header.kinds) == displayed_kind(name, kind),
                    "native header identity differs")
            text = header.rendered()
            require(all(token in text for token in assumptions(name)), "implicit assumptions absent")
            require("```" not in text and "```" not in info["doc"], "unsupported Markdown fence")
            require(bool(info["doc"].strip()), "public docstring absent")
            found[name] = kind
            rows.append(dict(name=name, kind=kind, header=text,
                             doc=info["doc"].strip(), path=path, line=info["line"]))
    require(found == EXPECTED, "missing public declaration")
    rows.sort(key=lambda row: (row["path"], row["line"]))
    lines = ["# Generated API reference", "",
             "This reference covers 128 authored public declarations of general-linear-groups.",
             "Import `GeneralLinearGroups` or the individual source module linked below.",
             "`MatrixTraceClient` and `PublicAPIClient` contain private checked clients, not public API.", "",
             "This page is not a private/generated-declaration census or proof audit.", "",
             "Headers below are native doc-gen4 display signatures, not complete declarations",
             "with proof bodies. Short names use the defining module's",
             "namespace, scoped notation and imports. Implicit parameters are displayed;",
             "universe variables retain their native names. Source links target this same checkout.", "",
             "The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).",
             "See [generation instructions](README.md) and the [mathematical overview](../README.md).", ""]
    for row in rows:
        lines += ["## " + row["name"], "", "```lean", row["header"], "```", "",
                  row["doc"], "", f"[Source](../{row['path']}#L{row['line']}) (line {row['line']}).", ""]
    markdown = "\n".join(lines).encode()
    manifest = dict(format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    adapter_sha256=digest(Path(__file__).read_bytes()),
                    analyzed_source_revision=revision, modules=list(MODULES),
                    inputs={p: digest(sources[p]) for p in sorted(sources)},
                    public_declarations=[r["name"] for r in rows],
                    native_record_sha256=native_hashes(records),
                    api_sha256=digest(markdown), proof_certification=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--native-data", type=Path, required=True,
                   help="native fromDb output doc-data directory")
    p.add_argument("--source-revision", required=True)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="compare retained outputs, never write")
    mode.add_argument("--refresh-binding", action="store_true",
                      help="author a new native snapshot; requires the selected Git source object")
    args = p.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.source_revision) is not None,
            "full source revision required")
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    records = {m: load_json(args.native_data / ("declaration-data-" + m + ".bmp"))
               for m in MODULES}
    if args.refresh_binding:
        # Explicit authoring mode for a genuinely new native run. Object equality
        # alone does not authenticate those records or approve their provenance.
        for path, raw in sources.items():
            old = subprocess.check_output(["git", "show", args.source_revision + ":" + path], cwd=root)
            require(old == raw, "source/pin drift from analyzed revision: " + path)
    else:
        # Portable reproduction must never silently absorb source/pin/record drift.
        # Exact commit/tree and native-run authentication stay in independent evidence.
        validate_binding(load_json(root / "docs/api-manifest.json"), args.source_revision,
                         sources, records)
    api, manifest = render(records, args.source_revision, sources)
    for name, raw in [("API.md", api), ("api-manifest.json", manifest)]:
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          declarations=len(EXPECTED), api_sha256=digest(api),
                          release_acceptance=False)))


if __name__ == "__main__":
    main()
