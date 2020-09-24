import argparse
from abc import abstractmethod, ABC
from typing import TextIO, NewType, MutableMapping, Tuple

Sid = NewType('Sid', int)
Nid = NewType('Nid', int)


def b2bv(t: Tuple[str, bool]) -> str:
    return '(ite {:s} #b1 #b0)'.format(t[0]) if t[1] else t[0]


def bv2b(t: Tuple[str, bool]) -> str:
    return t[0] if t[1] else '(= {:s} #b1)'.format(t[0])


class Node(ABC):
    symbol: str
    comment: str

    def __init__(self, symbol: str = None, comment: str = None):
        self.symbol = symbol
        self.comment = comment


class Sort(Node):
    sid: Sid

    def __init__(self, sid: Sid, symbol: str = None, comment: str = None):
        super().__init__(symbol, comment)
        self.sid = sid

    @abstractmethod
    def get_width(self) -> int:
        raise NotImplementedError

    @abstractmethod
    def to_smt_sort(self) -> str:
        raise NotImplementedError

    @abstractmethod
    def booleanizable(self) -> bool:
        raise NotImplementedError


class Bitvec(Sort):
    width: int

    def __init__(self, sid: Sid, width: int, symbol: str = None, comment: str = None):
        super().__init__(sid, symbol, comment)
        self.width = width

    def get_width(self) -> int:
        return self.width

    def to_smt_sort(self) -> str:
        return '(_ BitVec {:d})'.format(self.width)

    def booleanizable(self) -> bool:
        return self.width == 1


class Array(Sort):
    index: Sort
    element: Sort

    def __init__(self, sid: Sid, index: Sort, element: Sort, symbol: str = None, comment: str = None):
        super().__init__(sid, symbol, comment)
        self.index = index
        self.element = element

    def get_width(self) -> int:
        # TODO
        raise ValueError

    def to_smt_sort(self) -> str:
        return '(Array {:s} {:s})'.format(self.index.to_smt_sort(), self.element.to_smt_sort())

    def booleanizable(self) -> bool:
        return False


class Value(Node):
    nid: Nid
    sort: Sort

    def __init__(self, nid: Nid, sort: Sort, symbol: str = None, comment: str = None):
        super().__init__(symbol, comment)
        self.nid = nid
        self.sort = sort

    @abstractmethod
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        raise NotImplementedError


class Input(Value):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.nid in v_map:
            return v_map[self.nid]
        # TODO
        vid = 'i_{:d}'.format(self.nid)
        b = self.sort.booleanizable()
        v_map[self.nid] = vid, b
        return vid, b


class One(Value):
    def __init__(self, nid: Nid, sort: Sort, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        if sort is not Bitvec:
            # TODO
            raise ValueError

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.sort.booleanizable():
            return 'true', True
        return '#b' + '0' * (self.sort.get_width() - 1) + '1', False


class Ones(Value):
    def __init__(self, nid: Nid, sort: Sort, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        if sort is not Bitvec:
            # TODO
            raise ValueError

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.sort.booleanizable():
            return 'true', True
        return '#b' + '1' * self.sort.get_width(), False


class Zero(Value):
    def __init__(self, nid: Nid, sort: Sort, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        if sort is not Bitvec:
            # TODO
            raise ValueError

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.sort.booleanizable():
            return 'false', True
        return '#b' + '0' * self.sort.get_width(), False


class Const(Value):
    bin_str: str

    def __init__(self, nid: Nid, sort: Sort, bin_str: str, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.bin_str = bin_str
        if len(bin_str) > sort.get_width():
            # TODO
            raise ValueError

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.sort.booleanizable():
            return 'false' if self.bin_str == '0' else 'true', True
        return '#b' + self.bin_str.zfill(self.sort.get_width()), False


class Constd(Value):
    bin_str: str

    def __init__(self, nid: Nid, sort: Sort, dec_str: str, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        n: int = int(dec_str)
        if n < -1 << (sort.get_width() - 1) or n >= 1 << (sort.get_width() - 1):
            # TODO
            raise ValueError
        if n < 0:
            n = (1 << sort.get_width()) + n
        self.bin_str = format(n, 'b')

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.sort.booleanizable():
            return 'false' if self.bin_str == '0' else 'true', True
        return '#b' + self.bin_str.zfill(self.sort.get_width()), False


class Consth(Value):
    hex_str: str

    def __init__(self, nid: Nid, sort: Sort, hex_str: str, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.hex_str = hex_str
        if sort.get_width() % 4 != 0:
            # TODO:
            raise ValueError

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.sort.booleanizable():
            return 'false' if self.hex_str == '0' else 'true', True
        return '#x' + self.hex_str.zfill(self.sort.get_width() >> 2), False


class State(Value):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        if self.nid in v_map:
            return v_map[self.nid]
        # TODO
        vid = 's_{:d}'.format(self.nid)
        b = self.sort.booleanizable()
        v_map[self.nid] = vid, b
        return vid, b


class Sext(Value):
    value: Value
    w: int

    def __init__(self, nid: Nid, sort: Sort, value: Value, w: int, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.value = value
        self.w = w

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO: concat
        pass


class Uext(Value):
    value: Value
    w: int

    def __init__(self, nid: Nid, sort: Sort, value: Value, w: int, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.value = value
        self.w = w

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO: concat
        pass


class Slice(Value):
    value: Value
    upper: int
    lower: int

    def __init__(self, nid: Nid, sort: Sort, value: Value, upper: int, lower: int, symbol: str = None,
                 comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.value = value
        self.upper = upper
        self.lower = lower

    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO: extract
        pass


class UnaryOp(Value, ABC):
    value: Value

    def __init__(self, nid: Nid, sort: Sort, value: Value, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.value = value


class Not(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e, b = self.value.to_smt_expr(v_map)
        if b:
            return '(not {:s})'.format(e), True
        return '(bvnot {:s})'.format(e), False


class Inc(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Dec(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Neg(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e, b = self.value.to_smt_expr(v_map)
        if b:
            return e, True
        return '(bvneg {:s})'.format(e), False


class Redand(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e, b = self.value.to_smt_expr(v_map)
        if b:
            return e, True
        return '(= {:s} {:s})'.format(e, '#b' + '1' * self.sort.get_width()), True


class Redor(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e, b = self.value.to_smt_expr(v_map)
        if b:
            return e, True
        return '(distinct {:s} {:s})'.format(e, '#b' + '0' * self.sort.get_width()), True


class Redxor(UnaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class BinaryOp(Value, ABC):
    value1: Value
    value2: Value

    def __init__(self, nid: Nid, sort: Sort, value1: Value, value2: Value, symbol: str = None, comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.value1 = value1
        self.value2 = value2


class Iff(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(= {:s} {:s})'.format(bv2b(self.value1.to_smt_expr(v_map)), bv2b(self.value2.to_smt_expr(v_map))), True


class Implies(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(=> {:s} {:s})'.format(bv2b(self.value1.to_smt_expr(v_map)), bv2b(self.value2.to_smt_expr(v_map))), True


class Eq(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(= {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)), b2bv(self.value2.to_smt_expr(v_map))), True


class Neq(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(distinct {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                             b2bv(self.value2.to_smt_expr(v_map))), True


class Sgt(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsgt {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Ugt(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvugt {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Sgte(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsge {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Ugte(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvuge {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Slt(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvslt {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Ult(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvult {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Slte(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsle {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class Ulte(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvule {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), True


class And(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e1, b1 = t1 = self.value1.to_smt_expr(v_map)
        e2, b2 = t2 = self.value2.to_smt_expr(v_map)
        if b1 and b2:
            return '(and {:s} {:s})'.format(e1, e2), True
        return '(bvand {:s} {:s})'.format(b2bv(t1), b2bv(t2)), False


class Nand(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e1, b1 = t1 = self.value1.to_smt_expr(v_map)
        e2, b2 = t2 = self.value2.to_smt_expr(v_map)
        if b1 and b2:
            return '(not (and {:s} {:s}))'.format(e1, e2), True
        return '(bvand {:s} {:s})'.format(b2bv(t1), b2bv(t2)), False


class Nor(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e1, b1 = t1 = self.value1.to_smt_expr(v_map)
        e2, b2 = t2 = self.value2.to_smt_expr(v_map)
        if b1 and b2:
            return '(not (or {:s} {:s}))'.format(e1, e2), True
        return '(bvnor {:s} {:s})'.format(b2bv(t1), b2bv(t2)), False


class Or(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e1, b1 = t1 = self.value1.to_smt_expr(v_map)
        e2, b2 = t2 = self.value2.to_smt_expr(v_map)
        if b1 and b2:
            return '(or {:s} {:s})'.format(e1, e2), True
        return '(bvor {:s} {:s})'.format(b2bv(t1), b2bv(t2)), False


class Xnor(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvxnor {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Xor(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        e1, b1 = t1 = self.value1.to_smt_expr(v_map)
        e2, b2 = t2 = self.value2.to_smt_expr(v_map)
        if b1 and b2:
            return '(xor {:s} {:s})'.format(e1, e2), True
        return '(bvxor {:s} {:s})'.format(b2bv(t1), b2bv(t2)), False


class Sll(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvshl {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), False


class Sra(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvashr {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Srl(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvlshr {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Rol(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Ror(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Add(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvadd {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), False


class Mul(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvmul {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), False


class Sdiv(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsdiv {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Udiv(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvudiv {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Smod(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsmod {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Srem(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsrem {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Urem(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvurem {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Sub(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(bvsub {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                          b2bv(self.value2.to_smt_expr(v_map))), False


class Saddo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Uaddo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Sdivo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Udivo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Smulo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Umulo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Ssubo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Usubo(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        # TODO
        pass


class Concat(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(concat {:s} {:s})'.format(b2bv(self.value1.to_smt_expr(v_map)),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class Read(BinaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        return '(select {:s} {:s})'.format(self.value1.to_smt_expr(v_map),
                                           b2bv(self.value2.to_smt_expr(v_map))), False


class TernaryOp(Value, ABC):
    value1: Value
    value2: Value
    value3: Value

    def __init__(self, nid: Nid, sort: Sort, value1: Value, value2: Value, value3: Value, symbol: str = None,
                 comment: str = None):
        super().__init__(nid, sort, symbol, comment)
        self.value1 = value1
        self.value2 = value2
        self.value3 = value3


class Ite(TernaryOp):
    def to_smt_expr(self, v_map: MutableMapping[Nid, Tuple[str, bool]] = None) -> Tuple[str, bool]:
        pass
        # e2, b2 = self.value2.to_smt_expr(v_map)
        # e3, b3 = self.value3.to_smt_expr(v_map)
        # return '(ite {:s} {:s} {:s})'.format(bv2b(self.value1.to_smt_expr(v_map)), )


class Btor2Chc(object):
    def convert(self, source: TextIO, target: TextIO) -> None:
        pass


def main():
    parser: argparse.ArgumentParser = argparse.ArgumentParser(description='A tool to convert btor2 to CHC')
    parser.add_argument('--input', action='store', type=str, required=True)
    parser.add_argument('--output', action='store', type=str, required=True)
    args: argparse.Namespace = parser.parse_args()

    with open(args.input) as input_file:
        with open(args.output, 'w') as output_file:
            Btor2Chc().convert(input_file, output_file)


if __name__ == '__main__':
    main()
