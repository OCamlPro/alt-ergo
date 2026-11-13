from pygments.lexer import RegexLexer, words
from pygments.token import *

__globals__ = [ 'Smt2Lexer' ]

class Smt2Lexer(RegexLexer):
    """
    A SMT-LIB lexer.
    """
    name = 'SMT-LIB'
    url = 'https://smt-lib.org/'
    aliases = [ 'smt2' ]
    filenames = [ '*.smt2' ]
    mimetypes = [ 'text/x-smt2 ']

    keywords = (
        # Commands
        'assert', 'check-sat', 'check-sat-assuming', 'declare-const',
        'declare-datatype', 'declare-datatypes', 'declare-fun',
        'declare-sort', 'define-fun', 'define-fun-rec', 'define-funs-rec',
        'define-sort', 'echo', 'exit', 'get-assertions', 'get-assignment',
        'get-info', 'get-model', 'get-option', 'get-proof',
        'get-unsat-assumptions', 'get-unsat-core', 'get-value', 'pop', 'push',
        'reset', 'reset-assertions', 'set-info', 'set-logic', 'set-option',

        # Term builtins
        'let', 'forall', 'exists', 'match', '!', 'par', '_',
    )

    sorts = (
        'Int', 'Bool', 'Real', 'BitVec', 'Array', 'RoundingMode',
        'FloatingPoint', 'Float16', 'Float32', 'Float64', 'Float128',
    )

    constants = (
        # FloatingPoint
        '+oo', '-oo', '+zero', '-zero', 'NaN',
        'RNE', 'RNA', 'RTP', 'RTN', 'RTZ',
        'roundNearestTiesToEven', 'roundNearestTiesToAway',
        'roundTowardPositive', 'roundTowardNegative', 'roundTowardZero',
    )

    builtins = (
        # ArraysEx
        'select', 'store',

        # Bit-vectors
        'concat', 'extract', 'bvnot', 'bvneg',
        'bvand', 'bvor', 'bvxor', 'bvult', 'bvule', 'bvugt', 'bvuge',
        'bvslt', 'bvsle', 'bvsgt', 'bvsge', 'bvadd', 'bvmul', 'bvudiv',
        'bvsdiv', 'bvurem', 'bvsrem', 'bvshl', 'bvlshr', 'bvashr',
        'bvnand', 'bvnor', 'bvxnor','bvsub', 'repeat', 'zero_extend',
        'sign_extend', 'rotate_left', 'rotate_right',

        # Core
        'not', 'and', 'or', 'xor', 'distinct', 'ite',

        # Ints, Reals and Reals_Ints
        'div', 'mod', 'abs',
        'to_real', 'to_int', 'is_int',

        # FloatingPoint
        'fp', 'fp.abs', 'fp.neg', 'fp.add', 'fp.sub', 'fp.mul', 'fp.div',
        'fp.fma', 'fp.sqrt', 'fp.rem', 'fp.roundToIntegral', 'fp.min',
        'fp.max', 'fp.leq', 'fp.lt', 'fp.geq', 'fp.gt', 'fp.eq',
        'fp.isNormal', 'fp.isSubnormal', 'fp.isZero', 'fp.isInfinite',
        'fp.isNaN', 'fp.isNegative', 'fp.isPositive', 'to_fp',
        'to_fp_unsigned', 'fp.to_ubv', 'fp.to_sbv', 'fp.to_real',

        # Custom
        'ae.round',
        'ae.float16', 'ae.float32', 'ae.float64', 'ae.float128',
    )

    operators = (
        '=>', '=', '-', '+', '*', '/', '<', '<=', '>', '>=',
    )

    symbol = r'(?:(?:[a-zA-Z0-9+/*=%?!.$_~&^<>@-]+)|(?:\|[^\|]+\|))'

    symbol_suffix = r'(?![a-zA-Z0-9+/*=%?!.$_~&^<>@-])'

    tokens = {
        'root': [
            (r';.*$', Comment.Single),
            (r'\s+', Text),

            (r'[0-9]+', Number.Integer),
            (r'#x[0-9a-fA-F]+', Number.Integer.Hex),
            (r'#b[0-1]+', Number.Integer.Bin),
            (r'[0-9]+\.[0-9]+', Number.Float),
            (r'"([^"]|"")*"', String),
            (r':' + symbol, String.Symbol),

            (r'true|false', Name.Constant),
            (r'bv[0-9]+', Name.Constant),
            (words(constants, suffix=symbol_suffix), Name.Constant),
            (words(operators, suffix=symbol_suffix), Name.Operator),
            (words(keywords, suffix=symbol_suffix), Keyword),
            (words(sorts, suffix=symbol_suffix), Keyword.Type),
            (words(builtins, suffix=symbol_suffix), Keyword.Builtin),

            (symbol, Name),

            (r'[_()]', Punctuation),
        ],
    }
