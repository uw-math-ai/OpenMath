"""Central configuration for the Butcher textbook extraction pipeline."""
import re
from pathlib import Path

# ── Paths ──────────────────────────────────────────────────────────────
PROJECT_ROOT = Path("/Users/siyuange/Documents/OpenMath/extraction")
PDF_PATH = PROJECT_ROOT / "Butcher_J_Numerical_methods_for_ordinary_differ.pdf"
PDFTOTEXT = "/opt/homebrew/bin/pdftotext"
PDFTOHTML = "/opt/homebrew/bin/pdftohtml"
RAW_TEXT_DIR = PROJECT_ROOT / "raw_text"
KB_DIR = PROJECT_ROOT / "knowledge_base"
GRAPH_DIR = PROJECT_ROOT / "graph"
BLUEPRINT_DIR = PROJECT_ROOT.parent / "blueprint"

# ── Chapter metadata ───────────────────────────────────────────────────
# Butcher has 5 chapters (functioning as Parts), each with 2-digit
# sections and 3-digit subsections.
CHAPTERS = {
    1: {
        "title": "Differential and Difference Equations",
        "slug": "ch01_differential_difference",
        "sections": {
            10: "Differential Equation Problems",
            11: "Differential Equation Theory",
            12: "Further Evolutionary Problems",
            13: "Difference Equation Problems",
            14: "Difference Equation Theory",
        },
        "page_start": 1,
        "page_end": 49,
    },
    2: {
        "title": "Numerical Differential Equation Methods",
        "slug": "ch02_numerical_methods",
        "sections": {
            20: "The Euler Method",
            21: "Analysis of the Euler Method",
            22: "Generalizations of the Euler Method",
            23: "Runge\u2013Kutta Methods",
            24: "Linear Multistep Methods",
            25: "Taylor Series Methods",
            26: "Hybrid Methods",
            27: "Introduction to Implementation",
        },
        "page_start": 51,
        "page_end": 135,
    },
    3: {
        "title": "Runge\u2013Kutta Methods",
        "slug": "ch03_runge_kutta",
        "sections": {
            30: "Preliminaries",
            31: "Order Conditions",
            32: "Low Order Explicit Methods",
            33: "Runge\u2013Kutta Methods with Error Estimates",
            34: "Implicit Runge\u2013Kutta Methods",
            35: "Stability of Implicit Runge\u2013Kutta Methods",
            36: "Implementable Implicit Runge\u2013Kutta Methods",
            37: "Symplectic Runge\u2013Kutta Methods",
            38: "Algebraic Properties of Runge\u2013Kutta Methods",
            39: "Implementation Issues",
        },
        "page_start": 137,
        "page_end": 315,
    },
    4: {
        "title": "Linear Multistep Methods",
        "slug": "ch04_linear_multistep",
        "sections": {
            40: "Preliminaries",
            41: "The Order of Linear Multistep Methods",
            42: "Errors and Error Growth",
            43: "Stability Characteristics",
            44: "Order and Stability Barriers",
            45: "One-Leg Methods and G-stability",
            46: "Implementation Issues",
        },
        "page_start": 317,
        "page_end": 371,
    },
    5: {
        "title": "General Linear Methods",
        "slug": "ch05_general_linear",
        "sections": {
            50: "Representing Methods in General Linear Form",
            51: "Consistency, Stability and Convergence",
            52: "The Stability of General Linear Methods",
            53: "The Order of General Linear Methods",
            54: "Methods with Runge\u2013Kutta stability",
            55: "Methods with Inherent Runge\u2013Kutta Stability",
        },
        "page_start": 373,
        "page_end": 451,
    },
}

# Running headers as they appear in pdftotext output (uppercase, with
# possible ligature variants). Used to filter out repeated page headers.
RUNNING_HEADERS = {
    # Chapter titles (appear as running headers in uppercase)
    "DIFFERENTIAL AND DIFFERENCE EQUATIONS",
    "NUMERICAL DIFFERENTIAL EQUATION METHODS",
    "NUMERICAL METHODS FOR ORDINARY DIFFERENTIAL EQUATIONS",
    "RUNGE\u2013KUTTA METHODS",
    "LINEAR MULTISTEP METHODS",
    "GENERAL LINEAR METHODS",
    # With ligatures from pdftotext
    "RUNGE\u2013KUTTA METHODS",
    # Front/back matter
    "PREFACE TO THE FIRST EDITION",
    "PREFACE TO THE SECOND EDITION",
    "CONTENTS",
    "REFERENCES",
    "INDEX",
}

# ── Formal statement patterns ──────────────────────────────────────────
# Butcher uses 3-digit subsection number + uppercase letter:
# e.g., "Theorem 101A", "Definition 112A", "Lemma 310B"
THEOREM_DECL_RE = re.compile(
    r"^Theorem\s+(\d{3}[A-Z])\s*(.*)", re.DOTALL
)
DEFINITION_DECL_RE = re.compile(
    r"^De(?:fi|ﬁ)nition\s+(\d{3}[A-Z])\s*(.*)", re.DOTALL
)
LEMMA_DECL_RE = re.compile(
    r"^Lemma\s+(\d{3}[A-Z])\s*(.*)", re.DOTALL
)
COROLLARY_DECL_RE = re.compile(
    r"^Corollary\s+(?:(\d{3}[A-Z])\s*)?(.*)", re.DOTALL
)
PROOF_DECL_RE = re.compile(r"^Proof\.\s*(.*)", re.DOTALL)

# Section header: bold 2-digit number + title
# e.g., "10   Differential Equation Problems"
SECTION_HEADER_RE = re.compile(r"^(\d{2})\s{2,}(.+)")

# Subsection header: italic 3-digit number + title
# e.g., "100   Introduction to differential equations"
# In pdftotext, often appears as "100" alone on a line or "100  Title"
SUBSECTION_HEADER_RE = re.compile(r"^(\d{3})\s{2,}(.+)")
SUBSECTION_BARE_RE = re.compile(r"^(\d{3})\s*$")

# Exercises marker at end of sections
EXERCISES_RE = re.compile(r"^Exercises\s+(\d{2})\s*$")

# ── Equation patterns ──────────────────────────────────────────────────
# Equations numbered as (NNNx) where NNN is 3-digit subsection, x is letter
EQUATION_TAG_RE = re.compile(r"\((\d{3}[a-z])\)")

# ── Cross-reference patterns ──────────────────────────────────────────
FORMAL_REF_RE = re.compile(
    r"(Theorem|De(?:fi|ﬁ)nition|Lemma|Corollary)\s+(\d{3}[A-Z])"
)
SECTION_REF_RE = re.compile(
    r"(?:Section|Subsection|Chapter)\s+(\d{1,3})"
)
EQUATION_REF_RE = re.compile(r"\((\d{3}[a-z])\)")

# ── Inline definition patterns ─────────────────────────────────────────
# Phrases that introduce a concept definition with italic text
DEFINITION_INTRO_PATTERNS = [
    re.compile(r"is\s+said\s+to\s+be\s+(?:the\s+|a\s+|an\s+)?['\u2018]?([\w\s'''-]+?)['\u2019]?(?:\s+if\b|\s+when\b|[.,;:])"),
    re.compile(r"is\s+called\s+(?:the\s+|a\s+|an\s+)?['\u2018]?([\w\s'''-]+?)['\u2019]?(?:\s*[.,;:]|\s+and\s|\s+if\s|\s+\()"),
    re.compile(r"is\s+termed\s+(?:the\s+|a\s+)?['\u2018]?([\w\s-]+?)['\u2019]?(?:\s*[.,;:])"),
    re.compile(r"[Ww]e\s+say\s+that\b.*?\bis\s+['\u2018]?([\w\s'''-]+?)['\u2019]?(?:\s+if\b|\s+when\b|[.,;:])"),
    re.compile(r"[Ww]e\s+define\s+(?:the\s+)?['\u2018]?([\w\s-]+?)['\u2019]?(?:\s+as\s|\s+to\s+be\s|\s+by\s)"),
    re.compile(r"known\s+as\s+(?:the\s+|a\s+|an\s+)?['\u2018]?([\w\s'''-]+?)['\u2019]?(?:\s*[.,;:]|\s+and\s)"),
]

# ── Helper: derive chapter from a 3-digit subsection number ────────────
def chapter_from_subsection(subsec: int) -> int:
    """Return 1-5 from a 3-digit subsection number (100->1, 250->2, etc.)."""
    return subsec // 100

def chapter_from_section(sec: int) -> int:
    """Return 1-5 from a 2-digit section number (10->1, 25->2, etc.)."""
    return sec // 10

def section_from_subsection(subsec: int) -> int:
    """Return the 2-digit section from a 3-digit subsection (213->21)."""
    return subsec // 10


# Subsection titles (3-digit) extracted from TOC
SUBSECTION_TITLES = {
    100: "Introduction to differential equations",
    101: "The Kepler problem",
    102: "A problem arising from the method of lines",
    103: "The simple pendulum",
    104: "A chemical kinetics problem",
    105: "The Van der Pol equation and limit cycles",
    106: "The Lotka–Volterra problem and periodic orbits",
    107: "The Euler equations of rigid body rotation",
    110: "Existence and uniqueness of solutions",
    111: "Linear systems of differential equations",
    112: "Stiff differential equations",
    120: "Many-body gravitational problems",
    121: "Delay problems and discontinuous solutions",
    122: "Problems evolving on a sphere",
    123: "Further Hamiltonian problems",
    124: "Further differential-algebraic problems",
    130: "Introduction to difference equations",
    131: "A linear problem",
    132: "The Fibonacci difference equation",
    133: "Three quadratic problems",
    134: "Iterative solutions of a polynomial equation",
    135: "The arithmetic-geometric mean",
    140: "Linear difference equations",
    141: "Constant coefficients",
    142: "Powers of matrices",
    200: "Introduction to the Euler methods",
    201: "Some numerical experiments",
    202: "Calculations with stepsize control",
    203: "Calculations with mildly stiff problems",
    204: "Calculations with the implicit Euler method",
    210: "Formulation of the Euler method",
    211: "Local truncation error",
    212: "Global truncation error",
    213: "Convergence of the Euler method",
    214: "Order of convergence",
    215: "Asymptotic error formula",
    216: "Stability characteristics",
    217: "Local truncation error estimation",
    218: "Rounding error",
    220: "Introduction",
    221: "More computations in a step",
    222: "Greater dependence on previous values",
    223: "Use of higher derivatives",
    224: "Multistep–multistage–multiderivative methods",
    225: "Implicit methods",
    226: "Local error estimates",
    230: "Historical introduction",
    231: "Second order methods",
    232: "The coefficient tableau",
    233: "Third order methods",
    234: "Introduction to order conditions",
    235: "Fourth order methods",
    236: "Higher orders",
    237: "Implicit Runge–Kutta methods",
    238: "Stability characteristics",
    239: "Numerical examples",
    240: "Historical introduction",
    241: "Adams methods",
    242: "General form of linear multistep methods",
    243: "Consistency, stability and convergence",
    244: "Predictor–corrector Adams methods",
    245: "The Milne device",
    246: "Starting methods",
    247: "Numerical examples",
    250: "Introduction to Taylor series methods",
    251: "Manipulation of power series",
    252: "An example of a Taylor series solution",
    253: "Other methods using higher derivatives",
    254: "The use of f derivatives",
    255: "Further numerical examples",
    260: "Historical introduction",
    261: "Pseudo Runge–Kutta methods",
    262: "Generalized linear multistep methods",
    263: "General linear methods",
    264: "Numerical examples",
    270: "Choice of method",
    271: "Variable stepsize",
    272: "Interpolation",
    273: "Experiments with the Kepler problem",
    274: "Experiments with a discontinuous problem",
    300: "Rooted trees",
    301: "Functions on trees",
    302: "Some combinatorial questions",
    303: "The use of labelled trees",
    304: "Enumerating non-rooted trees",
    305: "Differentiation",
    306: "Taylor’s theorem",
    310: "Elementary differentials",
    311: "The Taylor expansion of the exact solution",
    312: "Elementary weights",
    313: "The Taylor expansion of the approximate solution",
    314: "Independence of the elementary differentials",
    315: "Conditions for order",
    316: "Order conditions for scalar problems",
    317: "Independence of elementary weights",
    318: "Local truncation error",
    319: "Global truncation error",
    320: "Methods of orders less than 4",
    321: "Simplifying assumptions",
    322: "Methods of order 4",
    323: "New methods from old",
    324: "Order barriers",
    325: "Methods of order 5",
    326: "Methods of order 6",
    327: "Methods of orders greater than 6",
    330: "Introduction",
    331: "Richardson error estimates",
    332: "Methods with built-in estimates",
    333: "A class of error-estimating methods",
    334: "The methods of Fehlberg",
    335: "The methods of Verner",
    336: "The methods of Dormand and Prince",
    340: "Introduction",
    341: "Solvability of implicit equations",
    342: "Methods based on Gaussian quadrature",
    343: "Reflected methods",
    344: "Methods based on Radau and Lobatto quadrature",
    350: "A-stability, A(α)-stability and L-stability",
    351: "Criteria for A-stability",
    352: "Padé approximations to the exponential function",
    353: "A-stability of Gauss and related methods",
    354: "Order stars",
    355: "Order arrows and the Ehle barrier",
    356: "AN-stability",
    357: "Non-linear stability",
    358: "BN-stability of collocation methods",
    359: "The V and W transformations",
    360: "Implementation of implicit Runge–Kutta methods",
    361: "Diagonally implicit Runge–Kutta methods",
    362: "The importance of high stage order",
    363: "Singly implicit methods",
    364: "Generalizations of singly implicit methods",
    365: "Effective order and DESIRE methods",
    370: "Maintaining quadratic invariants",
    371: "Examples of symplectic methods",
    372: "Order conditions",
    373: "Experiments with symplectic methods",
    380: "Motivation",
    381: "Equivalence classes of Runge–Kutta methods",
    382: "The group of Runge–Kutta methods",
    383: "The Runge–Kutta group",
    384: "A homomorphism between two groups",
    385: "A generalization of G1",
    386: "Recursive formula for the product",
    387: "Some special elements of G",
    388: "Some subgroups and quotient groups",
    389: "An algebraic interpretation of effective order",
    390: "Introduction",
    391: "Optimal sequences",
    392: "Acceptance and rejection of steps",
    393: "Error per step versus error per unit step",
    394: "Control-theoretic considerations",
    395: "Solving the implicit equations",
    400: "Fundamentals",
    401: "Starting methods",
    402: "Convergence",
    403: "Stability",
    404: "Consistency",
    405: "Necessity of conditions for convergence",
    406: "Sufficiency of conditions for convergence",
    410: "Criteria for order",
    411: "Derivation of methods",
    412: "Backward difference methods",
    420: "Introduction",
    421: "Further remarks on error growth",
    422: "The underlying one-step method",
    423: "Weakly stable methods",
    424: "Variable stepsize",
    430: "Introduction",
    431: "Stability regions",
    432: "Examples of the boundary locus method",
    433: "An example of the Schur criterion",
    434: "Stability of predictor–corrector methods",
    440: "Survey of barrier results",
    441: "Maximum order for a convergent k-step method",
    442: "Order stars for linear multistep methods",
    443: "Order arrows for linear multistep methods",
    450: "The one-leg counterpart to a linear multistep method",
    451: "The concept of G-stability",
    453: "Effective order interpretation",
    454: "Concluding remarks on G-stability",
    460: "Survey of implementation considerations",
    461: "Representation of data",
    462: "Variable stepsize for Nordsieck methods",
    463: "Local error estimation",
    500: "Multivalue–multistage methods",
    501: "Transformations of methods",
    502: "Runge–Kutta methods as general linear methods",
    503: "Linear multistep methods as general linear methods",
    504: "Some known unconventional methods",
    505: "Some recently discovered general linear methods",
    510: "Definitions of consistency and stability",
    511: "Covariance of methods",
    512: "Definition of convergence",
    513: "The necessity of stability",
    514: "The necessity of consistency",
    515: "Stability and consistency imply convergence",
    520: "Introduction",
    521: "Methods with maximal stability order",
    522: "Outline proof of the Butcher–Chipman conjecture",
    523: "Non-linear stability",
    524: "Reducible linear multistep methods and G-stability",
    525: "G-symplectic methods",
    530: "Possible definitions of order",
    531: "Local and global truncation errors",
    532: "Algebraic analysis of order",
    533: "An example of the algebraic approach to order",
    534: "The order of a G-symplectic method",
    535: "The underlying one-step method",
    540: "Design criteria for general linear methods",
    541: "The types of DIMSIM methods",
    542: "Runge–Kutta stability",
    543: "Almost Runge–Kutta methods",
    544: "Third order, three-stage ARK methods",
    545: "Fourth order, four-stage ARK methods",
    546: "A fifth order, five-stage method",
    547: "ARK methods for stiff problems",
    550: "Doubly companion matrices",
    551: "Inherent Runge–Kutta stability",
    552: "Conditions for zero spectral radius",
    553: "Derivation of methods with IRK stability",
    554: "Methods with property F",
    555: "Some non-stiff methods",
    556: "Some stiff methods",
    557: "Scale and modify for stability",
    558: "Scale and modify for error estimation",
}
