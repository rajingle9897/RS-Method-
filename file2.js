function Formula() 
{}
Formula.prototype.toString = function() 
{
    return this.string;
}
Formula.prototype.equals = function(fl1) 
{
    return this.string == fl1.string;
}
Formula.prototype.negate = function() 
{
    return new NegatedFormula(this);
}
Formula.prototype.unify = function(formula) 
{
    if (this.type != 'literal') 
        return false;
    if (this.sub && !formula.sub) 
        return false;
    if (this.sub) 
        return this.sub.unify(formula.sub);
    if (this.predicate != formula.predicate) 
        return false;
    if (this.terms.length != formula.terms.length) 
        return false;
    var merge = [];
    var items1 = this.terms.copyDeep();  
    var items2 = formula.terms.copyDeep();
    var i1, i2;
    while (i1 = items1.shift(), i2 = items2.shift()) 
    {
        log('unify terms? '+i1+' <=> '+i2);
        if (i1 == i2) 
        {   
            continue;
        }
        if (i1.isArray && i2.isArray) 
        {
            if (i1[0] != i2[0]) 
                return false;
            for (var i=1; i<i1.length; i++) 
            {
                items1.push(i1[i]);
                items2.push(i2[i]);
            }
            continue;
        }
        var i10 = (i1[0] == 'ξ' || i1[0] == 'ζ');
        var i20 = (i2[0] == 'ξ' || i2[0] == 'ζ');
        if (!i10 && !i20) 
        {
            log('no, neither term variable');
            return false;
        }
        if (!i10) 
        {
            var temp = i1; i1 = i2; i2 = temp; 
        }
        if (i2.isArray) 
        {
            var terms, termss = [i2];
            while (terms = termss.shift()) 
            {
                for (var i=0; i<terms.length; i++) 
                {
                    if (terms[i].isArray) 
                        termss.push(terms[i]);
                    else if (terms[i] == i1) 
                        return false;
                }
            }
        }
        log('yes: unify');
        var terms, termss = [merge, items1, items2];
        while (terms = termss.shift()) 
        {
            for (var i=0; i<terms.length; i++) 
            {
                if (terms[i].isArray) termss.push(terms[i]);
                else if (terms[i] == i1) terms[i] = i2;
            }
        }
        merge.push(i1); merge.push(i2);
    }
    return merge;
}
Formula.prototype.normalize = function() 
{
    var op = this.operator || this.quantifier;
    if (!op) 
        return this;
    switch (op) 
    {
        case '∧' : case '∨' : 
        {
            var sub1 = this.sub1.normalize();
            var sub2 = this.sub2.normalize();
            return new BinaryFormula(op, sub1, sub2);
        }
        case '→' : 
        {
            var sub1 = this.sub1.negate().normalize();
            var sub2 = this.sub2.normalize();
            return new BinaryFormula('∨', sub1, sub2);
        }
        case '↔' : 
        {
            var sub1 = new BinaryFormula('∧', this.sub1, this.sub2).normalize();
            var sub2 = new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate()).normalize();
            return new BinaryFormula('∨', sub1, sub2);
        }
        case '∀' : case '∃' : 
        {
            return new QuantifiedFormula(op, this.variable, this.matrix.normalize(),
               this.overWorlds);
        }
        case '□' : case '◇' : 
        {
            return new ModalFormula(op, this.sub.normalize());
        }
        case '¬' : 
        {
            var op2 = this.sub.operator || this.sub.quantifier;
            if (!op2) 
                return this;
            switch (op2) 
            {
                case '∧' : case '∨' : 
                {
                    var sub1 = this.sub.sub1.negate().normalize();
                    var sub2 = this.sub.sub2.negate().normalize();
                    var newOp = op2 == '∧' ? '∨' : '∧';
                    return new BinaryFormula(newOp, sub1, sub2);
                }
                case '→' : 
                {
                    var sub1 = this.sub.sub1.normalize();
                    var sub2 = this.sub.sub2.negate().normalize();
                    return new BinaryFormula('∧', sub1, sub2);
                }
                case '↔' : 
                {
                    var sub1 = new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate()).normalize();
                    var sub2 = new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2).normalize();
                    return new BinaryFormula('∨', sub1, sub2);
                }
                case '∀' : case '∃' : 
                {
                    var sub = this.sub.matrix.negate().normalize();
                    return new QuantifiedFormula(op2=='∀' ? '∃' : '∀', this.sub.variable, sub,
                       this.sub.overWorlds);
                }
                case '□' : case '◇' : 
                {
                    var sub = this.sub.sub.negate().normalize();
                    return new ModalFormula(op2=='□' ? '◇' : '□', sub);
                }
                case '¬' : 
                {
                    return this.sub.sub.normalize();
                }
            }
        }
    }
}
Formula.prototype.removeQuantifiers = function() 
{
    if (this.matrix) 
        return this.matrix.removeQuantifiers();
    if (this.sub1) 
    {
        var ns11 = this.sub1.quantifier ?
        this.sub1.matrix.removeQuantifiers() : this.sub1.removeQuantifiers();
        var ns12 = this.sub2.quantifier ?
        this.sub2.matrix.removeQuantifiers() : this.sub2.removeQuantifiers();
        if (this.sub1 == ns11 && this.sub2 == ns12) 
        	return this;
        var r1 = new BinaryFormula(this.operator, ns11, ns12);
        return r1;
    }
    return this;
}
Formula.prototype.alpha = function(n) 
{
    if (this.operator == '∧')
    {
        return n == 1 ? this.sub1 : this.sub2;
    }
    if (this.sub.operator == '∨') 
    {
        return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
    }
    if (this.sub.operator == '→') 
    {
        return n == 1 ? this.sub.sub1 : this.sub.sub2.negate();
    }
}
Formula.prototype.beta = function(n) 
{
    if (this.operator == '∨') 
    {
        return n == 1 ? this.sub1 : this.sub2;
    }
    if (this.operator == '→') 
    {
        return n == 1 ? this.sub1.negate() : this.sub2;
    }
    if (this.operator == '↔') 
    {
        return n == 1 ? new BinaryFormula('∧', this.sub1, this.sub2) : new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate())
    }
    if (this.sub.operator == '∧') 
    {
        return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
    }
    if (this.sub.operator == '↔') 
    {
        return n == 1 ? new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate()) :
        new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2)
    }
}
function AtomicFormula(predicate, terms) 
{
    this.type = 'literal';
    this.terms = terms; 
    this.predicate = predicate;
    this.string = predicate + AtomicFormula.items2string(terms);
}
AtomicFormula.items2string = function(list) 
{
    var r1 = '';
    for (var i=0; i<list.length; i++) 
    {
        if (list[i].isArray) 
        {
            var slist = list[i].copy();
            var fs = slist.shift();
            r1 += fs+'('+AtomicFormula.items2string(slist)+')';
        }
        else r1 += list[i];
    }
    return r1;
}
AtomicFormula.prototype = Object.create(Formula.prototype);
AtomicFormula.prototype.substitute = function(origTerm, newTerm, shallow) 
{
 if (typeof(origTerm) == 'string' && this.string.indexOf(origTerm) == -1) 
 {
    return this;
}
var newitems = AtomicFormula.substituteInTerms(this.terms, origTerm, newTerm, shallow);
if (!this.terms.equals(newitems)) 
{
    return new AtomicFormula(this.predicate, newitems);
}
else 
    return this;
}
AtomicFormula.substituteInTerms = function(terms, origTerm, newTerm, shallow) 
{
    var newitems = [];
    for (var j=0; j<terms.length; j++) 
    {
        var term = terms[j];
        if (term == origTerm) 
            newitems.push(newTerm);
        else if (term.isArray && !shallow) 
        {
            newitems.push(AtomicFormula.substituteInTerms(term, origTerm, newTerm));
        }
        else 
            newitems.push(term);
    }
    return newitems;
}
AtomicFormula.substituteInTerm = function(term, origTerm, newTerm) 
{
    if (term == origTerm) 
    	return newTerm;
    if (term.isArray) 
    	return AtomicFormula.substituteInTerms(term, origTerm, newTerm);
    return term;
}
function QuantifiedFormula(quantifier, variable, matrix, overWorlds) 
{
    this.quantifier = quantifier;
    this.matrix = matrix;
    this.overWorlds = overWorlds;
    this.variable = variable; 
    if (overWorlds) 
    {
        this.type = quantifier == '∀' ? 'modalGamma' : 'modalDelta';
    }
    else 
    {
        this.type = quantifier == '∀' ? 'gamma' : 'delta';
    }
    this.string = quantifier + variable + matrix;
}
QuantifiedFormula.prototype = Object.create(Formula.prototype);
QuantifiedFormula.prototype.substitute = function(origTerm, newTerm, shallow) 
{
    if (this.variable == origTerm) 
        return this;
    var nmat = this.matrix.substitute(origTerm, newTerm, shallow);
    if (nmat == this.matrix) 
        return this;
    return new QuantifiedFormula(this.quantifier, this.variable, nmat, this.overWorlds);
}
function BinaryFormula(operator, sub1, sub2) 
{
    this.operator = operator;
    this.sub1 = sub1;
    this.sub2 = sub2;
    this.type = operator == '∧' ? 'alpha' : 'beta';
    this.string = '(' + sub1 + operator + sub2 + ')';
}
BinaryFormula.prototype = Object.create(Formula.prototype);
BinaryFormula.prototype.substitute = function(origTerm, newTerm, shallow) 
{
    var ns11 = this.sub1.substitute(origTerm, newTerm, shallow);
    var ns12 = this.sub2.substitute(origTerm, newTerm, shallow);
    if (this.sub1 == ns11 && this.sub2 == ns12) 
        return this;
    return new BinaryFormula(this.operator, ns11, ns12);
}
function ModalFormula(operator, sub) 
{
    this.operator = operator;
    this.sub = sub;
    this.type = operator == '□' ? 'modalGamma' : 'modalDelta';
    this.string = operator + sub;
}
ModalFormula.prototype = Object.create(Formula.prototype);
ModalFormula.prototype.substitute = function(origTerm, newTerm, shallow) 
{
    var ns1 = this.sub.substitute(origTerm, newTerm, shallow);
    if (this.sub == ns1) 
        return this;
    return new ModalFormula(this.operator, ns1);
}
function NegatedFormula(sub) 
{
    this.operator = '¬';
    this.sub = sub;
    this.type = NegatedFormula.computeType(sub);
    this.string = '¬' + sub;
}
NegatedFormula.computeType = function(sub) 
{
    if (sub.operator == '¬') 
        return 'doublenegation';
    switch (sub.type) 
    {
        case 'literal': { return 'literal'; }
        case 'alpha': { return 'beta'; }
        case 'beta': { return sub.operator == '↔' ? 'beta' : 'alpha'; }
        case 'gamma': { return 'delta'; }
        case 'delta': { return 'gamma'; }
        case 'modalGamma': { return 'modalBeta'; }
        case 'modalDelta': { return 'modalGamma'; }
    }
}
NegatedFormula.prototype = Object.create(Formula.prototype);
NegatedFormula.prototype.substitute = function(origTerm, newTerm, shallow) 
{
    var ns1 = this.sub.substitute(origTerm, newTerm, shallow);
    if (this.sub == ns1) 
        return this;
    return new NegatedFormula(ns1);
}