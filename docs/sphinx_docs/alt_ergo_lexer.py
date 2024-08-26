from pygments.lexer import RegexLexer, include
from pygments.token import String, Text, Name, Comment,\
    Keyword, Operator, Number

__globals__ = [ 'AltErgoLexer' ]

class AltErgoLexer(RegexLexer):
    """
    For the Alt-Ergo language.
    """

    name = 'Alt-Ergo'
    url = 'https://alt-ergo.ocamlpro.com/'
    aliases = ['alt-ergo']
    filenames = ['*.ae']
    mimetypes = ['text/x-alt-ergo']

    keywords = (
        'ac', 'axiom', 'bitv', 'case_split', 'check', 'cut',
        'distinct', 'else', 'end', 'exists', 'extends', 'forall',
        'function', 'goal', 'check_sat', 'if', 'let', 'logic', 'not',
        'predicate', 'prop', 'rewriting', 'then', 'theory',
        'type', 'match', 'with', 'of',
    )
    keyopts = (
        r',', r';', r'\(', r'\)', r':', r'->', r'<-', r'<->', r'=', r'<', r'<=',
        r'>', r'>=', r'<>', r'\+', r'-', r'\*', r'\*\*', r'\*\*\.', r'/', r'%',
        r'@', r'\.', r'#', r'\[', r'\]', r'\{', r'\}', r'\|', r'\^', r'\|->',
    )

    word_operators = ('and', 'in', 'or', 'xor')
    primitives = ('bool', 'int', 'real', 'unit', 'void')

    tokens = {
        'escape-sequence': [
            (r'\\[\\"\'ntbr]', String.Escape),
            (r'\\[0-9]{3}', String.Escape),
            (r'\\x[0-9a-fA-F]{2}', String.Escape),
        ],
        'root': [
            (r'\s+', Text),
            (r'false|true', Name.Builtin.Pseudo),
            (r'\(\*(?![)])', Comment, 'comment'),
            (r'\b(%s)\b' % '|'.join(keywords), Keyword),
            (r'(%s)' % '|'.join(keyopts[::-1]), Operator),
            (r'\b(%s)\b' % '|'.join(word_operators), Operator.Word),
            (r'\b(%s)\b' % '|'.join(primitives), Keyword.Type),

            (r"\??[^\W\d][\w?']*", Name),

            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'0[oO][0-7][0-7_]*', Number.Oct),
            (r'0[bB][01][01_]*', Number.Bin),
            (r'\d[\d_]*', Number.Integer),

            (r"'", Keyword),

            (r'"', String.Double, 'string'),
        ],
        'comment': [
            (r'[^(*)]+', Comment),
            (r'\(\*', Comment, '#push'),
            (r'\*\)', Comment, '#pop'),
            (r'[(*)]', Comment),
        ],
        'string': [
            (r'[^\\"]+', String.Double),
            include('escape-sequence'),
            (r'\\\n', String.Double),
            (r'"', String.Double, '#pop'),
        ],
    }
