#!/usr/bin/env python3
"""
Parser for the instruction outlawing DSL.

Grammar:
    program = { rule }
    rule = instruction_rule | pattern_rule | comment
    instruction_rule = "instruction" identifier [ field_constraints ]
    pattern_rule = "pattern" hex_value "mask" hex_value [ description ]
    field_constraints = "{" field_constraint { "," field_constraint } "}"
    field_constraint = field_name "=" field_value
    field_value = wildcard | number | register_name
"""

import re
import sys
from dataclasses import dataclass
from typing import List, Optional, Dict, Union
from enum import Enum

# ============================================================================
# Token Types
# ============================================================================

class TokenType(Enum):
    # Keywords
    INSTRUCTION = "instruction"
    PATTERN = "pattern"
    MASK = "mask"

    # Literals
    IDENTIFIER = "identifier"
    NUMBER = "number"
    WILDCARD = "wildcard"

    # Symbols
    LBRACE = "{"
    RBRACE = "}"
    COMMA = ","
    EQUALS = "="

    # Other
    COMMENT = "comment"
    NEWLINE = "newline"
    EOF = "eof"

@dataclass
class Token:
    type: TokenType
    value: any
    line: int
    column: int

# ============================================================================
# AST Nodes
# ============================================================================

@dataclass
class FieldConstraint:
    """Represents a field constraint like 'rd = x5' or 'opcode = 0x33'"""
    field_name: str
    field_value: Union[str, int]  # Can be wildcard "*", register "x5", or number

@dataclass
class InstructionRule:
    """High-level instruction rule like 'instruction MUL { rd = x0 }'"""
    name: str
    constraints: List[FieldConstraint]
    line: int

@dataclass
class PatternRule:
    """Low-level pattern rule like 'pattern 0x02000033 mask 0xFE00707F'"""
    pattern: int
    mask: int
    description: Optional[str]
    line: int

@dataclass
class Program:
    """Root AST node containing all rules"""
    rules: List[Union[InstructionRule, PatternRule]]

# ============================================================================
# Lexer
# ============================================================================

class Lexer:
    def __init__(self, text: str):
        self.text = text
        self.pos = 0
        self.line = 1
        self.column = 1
        self.tokens = []

    def error(self, msg: str):
        raise SyntaxError(f"Lexer error at line {self.line}, column {self.column}: {msg}")

    def peek(self, offset=0):
        pos = self.pos + offset
        if pos < len(self.text):
            return self.text[pos]
        return None

    def advance(self):
        if self.pos < len(self.text):
            if self.text[self.pos] == '\n':
                self.line += 1
                self.column = 1
            else:
                self.column += 1
            self.pos += 1

    def skip_whitespace(self):
        while self.peek() and self.peek() in ' \t\r':
            self.advance()

    def read_comment(self):
        """Read a comment starting with #"""
        start_line = self.line
        start_col = self.column
        self.advance()  # skip #

        comment = ""
        while self.peek() and self.peek() != '\n':
            comment += self.peek()
            self.advance()

        return Token(TokenType.COMMENT, comment.strip(), start_line, start_col)

    def read_number(self):
        """Read a number (hex, binary, or decimal)"""
        start_line = self.line
        start_col = self.column

        num_str = ""

        # Check for hex (0x) or binary (0b)
        if self.peek() == '0' and self.peek(1) in 'xXbB':
            num_str += self.peek()
            self.advance()
            num_str += self.peek()
            self.advance()

            if num_str[1] in 'xX':
                # Hex
                while self.peek() and self.peek() in '0123456789abcdefABCDEF_':
                    if self.peek() != '_':
                        num_str += self.peek()
                    self.advance()
                value = int(num_str, 16)
            else:
                # Binary
                while self.peek() and self.peek() in '01_':
                    if self.peek() != '_':
                        num_str += self.peek()
                    self.advance()
                value = int(num_str, 2)
        else:
            # Decimal
            while self.peek() and self.peek() in '0123456789_':
                if self.peek() != '_':
                    num_str += self.peek()
                self.advance()
            value = int(num_str)

        return Token(TokenType.NUMBER, value, start_line, start_col)

    def read_identifier(self):
        """Read an identifier or keyword"""
        start_line = self.line
        start_col = self.column

        ident = ""
        while self.peek() and (self.peek().isalnum() or self.peek() in '_.-'):
            ident += self.peek()
            self.advance()

        # Check if it's a keyword
        if ident == "instruction":
            return Token(TokenType.INSTRUCTION, ident, start_line, start_col)
        elif ident == "pattern":
            return Token(TokenType.PATTERN, ident, start_line, start_col)
        elif ident == "mask":
            return Token(TokenType.MASK, ident, start_line, start_col)
        else:
            return Token(TokenType.IDENTIFIER, ident, start_line, start_col)

    def tokenize(self) -> List[Token]:
        """Tokenize the entire input"""
        tokens = []

        while self.pos < len(self.text):
            self.skip_whitespace()

            if not self.peek():
                break

            ch = self.peek()

            # Comments
            if ch == '#':
                tokens.append(self.read_comment())
                continue

            # Newlines
            if ch == '\n':
                line = self.line
                col = self.column
                self.advance()
                tokens.append(Token(TokenType.NEWLINE, '\n', line, col))
                continue

            # Single character tokens
            if ch == '{':
                tokens.append(Token(TokenType.LBRACE, ch, self.line, self.column))
                self.advance()
                continue

            if ch == '}':
                tokens.append(Token(TokenType.RBRACE, ch, self.line, self.column))
                self.advance()
                continue

            if ch == ',':
                tokens.append(Token(TokenType.COMMA, ch, self.line, self.column))
                self.advance()
                continue

            if ch == '=':
                tokens.append(Token(TokenType.EQUALS, ch, self.line, self.column))
                self.advance()
                continue

            # Wildcards
            if ch in '*x_' and (not self.peek(1) or not self.peek(1).isalnum()):
                tokens.append(Token(TokenType.WILDCARD, ch, self.line, self.column))
                self.advance()
                continue

            # Numbers
            if ch.isdigit():
                tokens.append(self.read_number())
                continue

            # Identifiers and keywords
            if ch.isalpha() or ch == '_':
                tokens.append(self.read_identifier())
                continue

            self.error(f"Unexpected character: {ch}")

        tokens.append(Token(TokenType.EOF, None, self.line, self.column))
        return tokens

# ============================================================================
# Parser
# ============================================================================

class Parser:
    def __init__(self, tokens: List[Token]):
        self.tokens = [t for t in tokens if t.type not in (TokenType.NEWLINE, TokenType.COMMENT)]
        self.pos = 0

    def error(self, msg: str):
        if self.pos < len(self.tokens):
            tok = self.tokens[self.pos]
            raise SyntaxError(f"Parser error at line {tok.line}, column {tok.column}: {msg}")
        else:
            raise SyntaxError(f"Parser error at end of file: {msg}")

    def peek(self, offset=0) -> Optional[Token]:
        pos = self.pos + offset
        if pos < len(self.tokens):
            return self.tokens[pos]
        return None

    def advance(self) -> Token:
        tok = self.peek()
        self.pos += 1
        return tok

    def expect(self, token_type: TokenType) -> Token:
        tok = self.peek()
        if not tok or tok.type != token_type:
            self.error(f"Expected {token_type}, got {tok.type if tok else 'EOF'}")
        return self.advance()

    def parse(self) -> Program:
        """Parse the entire program"""
        rules = []

        while self.peek() and self.peek().type != TokenType.EOF:
            rule = self.parse_rule()
            if rule:
                rules.append(rule)

        return Program(rules)

    def parse_rule(self) -> Optional[Union[InstructionRule, PatternRule]]:
        """Parse a single rule"""
        tok = self.peek()

        if not tok or tok.type == TokenType.EOF:
            return None

        if tok.type == TokenType.INSTRUCTION:
            return self.parse_instruction_rule()
        elif tok.type == TokenType.PATTERN:
            return self.parse_pattern_rule()
        else:
            self.error(f"Expected 'instruction' or 'pattern', got {tok.type}")

    def parse_instruction_rule(self) -> InstructionRule:
        """Parse: instruction IDENTIFIER [ field_constraints ]"""
        instr_tok = self.expect(TokenType.INSTRUCTION)
        name_tok = self.expect(TokenType.IDENTIFIER)

        constraints = []
        if self.peek() and self.peek().type == TokenType.LBRACE:
            constraints = self.parse_field_constraints()

        return InstructionRule(name_tok.value, constraints, instr_tok.line)

    def parse_pattern_rule(self) -> PatternRule:
        """Parse: pattern NUMBER mask NUMBER [ COMMENT ]"""
        pattern_tok = self.expect(TokenType.PATTERN)
        pattern_num = self.expect(TokenType.NUMBER)
        self.expect(TokenType.MASK)
        mask_num = self.expect(TokenType.NUMBER)

        # Description would have been captured as a comment token (already filtered out)
        # We can't easily get it here, so leave as None for now

        return PatternRule(pattern_num.value, mask_num.value, None, pattern_tok.line)

    def parse_field_constraints(self) -> List[FieldConstraint]:
        """Parse: { field_constraint , field_constraint , ... }"""
        self.expect(TokenType.LBRACE)

        constraints = []

        # First constraint
        constraints.append(self.parse_field_constraint())

        # Additional constraints
        while self.peek() and self.peek().type == TokenType.COMMA:
            self.advance()  # skip comma
            constraints.append(self.parse_field_constraint())

        self.expect(TokenType.RBRACE)

        return constraints

    def parse_field_constraint(self) -> FieldConstraint:
        """Parse: field_name = field_value"""
        field_name = self.expect(TokenType.IDENTIFIER)
        self.expect(TokenType.EQUALS)

        # Parse field value (wildcard, number, or identifier)
        value_tok = self.peek()

        if value_tok.type == TokenType.WILDCARD:
            value = self.advance().value
        elif value_tok.type == TokenType.NUMBER:
            value = self.advance().value
        elif value_tok.type == TokenType.IDENTIFIER:
            value = self.advance().value
        else:
            self.error(f"Expected field value, got {value_tok.type}")

        return FieldConstraint(field_name.value, value)

# ============================================================================
# Main / Testing
# ============================================================================

def parse_dsl(text: str) -> Program:
    """Parse DSL text and return AST"""
    lexer = Lexer(text)
    tokens = lexer.tokenize()
    parser = Parser(tokens)
    return parser.parse()

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Parse and validate instruction outlawing DSL files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  # Parse and validate a DSL file
  python3 instruction_dsl_parser.py my_rules.dsl

  # Parse and show verbose output
  python3 instruction_dsl_parser.py my_rules.dsl -v

  # Run built-in test
  python3 instruction_dsl_parser.py --test

DSL Syntax:
  instruction <NAME> [ { <field>=<value>, ... } ]
  pattern <hex> mask <hex>

  Example:
    instruction MUL
    instruction ADD { rd = x0 }
    pattern 0x02000033 mask 0xFE00707F
        '''
    )

    parser.add_argument('file', nargs='?', help='DSL file to parse')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Show detailed parse output')
    parser.add_argument('--test', action='store_true',
                       help='Run built-in test instead of parsing a file')

    args = parser.parse_args()

    # Built-in test mode
    if args.test:
        test_input = """
        # Outlaw all multiply instructions
        instruction MUL
        instruction MULH

        # Outlaw MUL with specific register constraint
        instruction MUL { rd = x0 }

        # Low-level pattern
        pattern 0x02000033 mask 0xFE00707F

        # Multiple constraints
        instruction ADD { rd = x0, rs1 = x1 }
        """

        try:
            ast = parse_dsl(test_input)
            print("✓ Built-in test passed!")
            print(f"Found {len(ast.rules)} rules:")
            for rule in ast.rules:
                print(f"  {rule}")
        except SyntaxError as e:
            print(f"✗ Test failed: {e}")
            sys.exit(1)
        return

    # File parsing mode
    if not args.file:
        parser.print_help()
        sys.exit(1)

    try:
        with open(args.file, 'r') as f:
            dsl_text = f.read()
    except FileNotFoundError:
        print(f"Error: File '{args.file}' not found")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading file: {e}")
        sys.exit(1)

    # Parse the file
    try:
        ast = parse_dsl(dsl_text)
        print(f"✓ Parsed {args.file} successfully!")
        print(f"Found {len(ast.rules)} rules")

        if args.verbose:
            print("\nRules:")
            for i, rule in enumerate(ast.rules, 1):
                print(f"\n{i}. {type(rule).__name__}:")
                if isinstance(rule, InstructionRule):
                    print(f"   Name: {rule.name}")
                    if rule.constraints:
                        print(f"   Constraints:")
                        for c in rule.constraints:
                            print(f"     - {c.field_name} = {c.field_value}")
                elif isinstance(rule, PatternRule):
                    print(f"   Pattern: 0x{rule.pattern:08x}")
                    print(f"   Mask:    0x{rule.mask:08x}")
                    if rule.description:
                        print(f"   Description: {rule.description}")
        else:
            # Summary
            instr_count = sum(1 for r in ast.rules if isinstance(r, InstructionRule))
            pattern_count = sum(1 for r in ast.rules if isinstance(r, PatternRule))
            print(f"  - {instr_count} instruction rules")
            print(f"  - {pattern_count} pattern rules")
            print("\nUse -v for detailed output")

    except SyntaxError as e:
        print(f"✗ Parse error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
