function ModelFinder(initFormulas, parser, accessibilityConstraints, s5){
    log("*** creating ModelFinder");

    this.parser = parser;
    this.s5 = s5;
    
    if (s5) {
        accessibilityConstraints = [];
        initFormulas = initFormulas.map(function(f) {
            return parser.stripAccessibilityClauses(f);
        });
    }
    this.predicates = parser.getSymbols('predicate');
    if (s5) this.predicates.remove(parser.R);
    this.constants = parser.getSymbols('individual constant');
    this.funcSymbols = parser.getSymbols('function symbol');
    if (parser.isModal) {
        this.constants.unshift(parser.w);
    }
    initFormulas = initFormulas.concat(accessibilityConstraints || []);
    this.clauses = this.getClauses(initFormulas);
    var IndividualsNum = 1;
    var WorldsNum = this.parser.isModal ? 1 : 0;
    this.model = new Model(this, IndividualsNum, WorldsNum);
    
    this.alternativeModels = [];
}

ModelFinder.prototype.getClauses = function(formulas) {
    var res = [];
    for (var i=0; i<formulas.length; i++) {
        var formula = formulas[i]; 
        log('getting clauses from '+formula);
        var clauses = this.parser.clausalNormalForm(formula);
        res = res.concatNoDuplicates(clauses);
    }
    log('all clauses: '+res);
    res = this.simplifyClauses(res);
    log('simplified clauses: '+res);
    return res;
}

ModelFinder.prototype.simplifyClauses = function(clauseList) {
    var bm = clauseList.filter(function(clause) {
        for (var i=0; i<clause.length; i++) {
            for (var j=i+1; j<clause.length; j++) {
                if (clause[i].sub && clause[i].sub.string == clause[j].string ||
                    clause[j].sub && clause[j].sub.string == clause[i].string) {
                    return false;
                }
            }
        }
        return true;
    });
    var bm = bm.map(function(clause) {
        return clause.removeDuplicates();
    });
    bm.sort(function(a,b){ return a.length > b.length; });
    if (bm.length > 5000) return bm;
    bm2 = bm.copy();
    var literals_to_clauses = {};
    for (var i=0; i<bm.length; i++) {
        for (var k=0; k<bm[i].length; k++) {
            var lit = bm[i][k].string;
            if (!literals_to_clauses[lit]) literals_to_clauses[lit] = [bm[i]];
            else literals_to_clauses[lit].push(bm[i]);
        }
    }
    for (var i=0; i<bm.length; i++) {
        var clause = bm[i];
        var lit = clause[0].string;
        var supersets = literals_to_clauses[lit];
        for (var k=1; k<clause.length && supersets.length; k++) {
            lit = clause[k].string;
            supersets.intersect(literals_to_clauses[lit]);
        }
        for (var k=0; k<supersets.length; k++) {
            if (bm.indexOf(supersets[k]) > bm.indexOf(clause)) {
                bm2.remove(supersets[k]);
            }
        }
    }
    return bm2;
}

ModelFinder.prototype.nextStep = function() {

    if (this.model.clauses.length == 0) return true;
    var literal = this.model.clauses[0][0];
    log("** modelfinder: "+this.model.clauses);
    log(this.model.curIntToString());
    if (!literal) {
        this.backtrack();
        return false;
    }
    log("trying to satisfy "+literal);
    if (!this.model.termValues) {
        this.model.initTermValues(literal);
    }
    else {
        if (!this.model.iterateTermValues()) {
            log("no more term interpretations to try: giving up");
            this.model.clauses[0].shift();
            this.model.termValues = null;
            return false;
        }
    }
    
    while (true) {
        var atom = literal.sub || literal;
        var nterms = this.model.reduceTerms(atom.terms);
        var redAtom = atom.predicate+nterms.toString();
        if (this.model.curInt[redAtom] === (atom != literal)) {
            log("literal is false on present term interpretation");
            if (!this.model.iterateTermValues()) {
                log("no more term interpretations to try: giving up");
                this.model.clauses[0].shift();
                this.model.termValues = null;
                return false;
            }
        }
        else {
            this.alternativeModels.push(this.model.copy());
            if (this.model.curInt[redAtom] === undefined) {
                log('setting value for '+redAtom+' to '+(atom==literal));
                this.model.curInt[redAtom] = (atom==literal);
            }
            log("literal is satisfied: "+redAtom+" -> "+this.model.curInt[redAtom]);
            this.model.interpretation = this.model.curInt;
            this.model.termValues = null;
            this.model.clauses.shift();
            this.model.simplifyRemainingClauses();
            return this.model.clauses.length == 0;
        }
    }
}

ModelFinder.prototype.backtrack = function() {
    log("backtracking");
    if (this.alternativeModels.length == 0) {
        log("no more models to backtrack; initializing larger model");
        var WorldsNum = this.model.worlds.length;
        var IndividualsNum = this.model.domain.length;
        if (WorldsNum && this.parser.isPropositional) {
            WorldsNum++;
        }
        else {
            if (WorldsNum && WorldsNum < this.model.domain.length) {
                WorldsNum++;
            }
            else IndividualsNum++; 
        }
        this.model = new Model(this, IndividualsNum, WorldsNum);
    }
    else {
        this.model = this.alternativeModels.pop();
        this.model.curInt = {};
        for (var p in this.model.interpretation) {
            this.model.curInt[p] = this.model.interpretation[p];
        }
        var tv = this.model.termValues;
        for (var i=0; i<tv.length; i++) {
            var redTerm = this.model.reduceArguments(tv[i][0]).toString();
            if (tv[i][3] !== null) {
                this.model.curInt[redTerm] = tv[i][3];
            }
        }
    }
}


function Model(modelfinder, IndividualsNum, WorldsNum) {

    if (!modelfinder) { 
        return;
    }
    
    this.modelfinder = modelfinder;
    this.parser = modelfinder.parser;
    this.domain = Array.getArrayOfNumbers(IndividualsNum);
    this.worlds = Array.getArrayOfNumbers(WorldsNum);
    this.isModal = WorldsNum > 0;
    log('model domain '+this.domain+', worlds '+this.worlds);

    this.interpretation = {}; 

    this.clauses = this.getDomainClauses();
    
    this.termValues = null;

    this.curInt = {};
}

Model.prototype.initTermValues = function(literal) {

    log("initializing termValues");
    
    var atom = literal.sub || literal;
    var termIsOld = {};
    var terms = [];
    
    for (var i=0; i<atom.terms.length; i++) {
        if (typeof atom.terms[i] == 'number') continue;
        var termStr = atom.terms[i].toString();
        if (termIsOld[termStr]) continue;
        termIsOld[termStr] = true;
        var maxValue = this.domain.length - 1;
        if (this.parser.isModal) {
            if (i == atom.terms.length-1 || atom.predicate == this.parser.R) {
                maxValue = this.worlds.length - 1;
            }
        }
        terms.push([atom.terms[i], termStr, maxValue, null]);
    }
    for (var i=0; i<terms.length; i++) {
        if (terms[i][0].isArray) {
            var maxValue = terms[i][2];
            for (var j=1; j<terms[i][0].length; j++) {
                var subTerm = terms[i][0][j];
                if (typeof subTerm == 'number') continue;
                var termStr = subTerm.toString();
                if (termIsOld[termStr]) continue;
                termIsOld[termStr] = true;
                terms.push([subTerm, termStr, maxValue, null]);
            }
        }
    }

    terms.sort(function(a,b){
        return a[1].length > b[1].length;
    });
    this.curInt = {};
    for (var p in this.interpretation) {
        this.curInt[p] = this.interpretation[p];
    }
    for (var i=0; i<terms.length; i++) {
        var redTerm = this.reduceArguments(terms[i][0]).toString();
        if (!(redTerm in this.curInt)) {
            terms[i][3] = 0;
            this.curInt[redTerm] = 0;
        }
    }

    this.termValues = terms;
    log(this.termValues);
}

Model.prototype.reduceArguments = function(term) {
    if (term.isArray) {
        var nterm = this.reduceTerms(term, 1);
        nterm.unshift(term[0]);
        return nterm;
    }
    return term;
}

Model.prototype.reduceTerms = function(terms, startIndex) {
    var res = [];
    for (var i=(startIndex || 0); i<terms.length; i++) {
        if (typeof terms[i] == 'number') {
            res.push(terms[i]);
        }
        else if (terms[i].isArray) {
            var nterm = this.reduceTerms(terms[i], 1);
            nterm.unshift(terms[i][0]);
            var ntermStr = nterm.toString();
            if (ntermStr in this.curInt) {
                res.push(this.curInt[ntermStr]);
            }
            else {
                res.push(nterm);
            }
        }
        else {
            if (terms[i] in this.curInt) {
                res.push(this.curInt[terms[i]]);
            }
            else {
                res.push(terms[i]);
            }
        }
    }
    return res;
}

Model.prototype.iterateTermValues = function() {
    log("trying to iterate termValues");
    for (var i=this.termValues.length-1; i>=0; i--) {
        var tv = this.termValues[i];
        if (tv[3] === null || tv[3] == tv[2]) {
            continue;
        }
        tv[3]++;
        var redTerm = this.reduceArguments(tv[0]).toString();
        this.curInt[redTerm] = tv[3];
        log('set '+redTerm+' to '+tv[3]);
        for (var j=i+1; j<this.termValues.length; j++) {
            var redTerm = this.reduceArguments(this.termValues[j][0]).toString();
            if (this.curInt[redTerm] === undefined) {
                this.termValues[j][3] = 0;
                this.curInt[redTerm] = 0;
            }
            else {
                this.termValues[j][3] = null;
            }
        }
        log(this.termValues);
        return true;
    }
    return false;
}

Model.prototype.satisfy = function(literal) {
    var atom = literal.sub || literal;
    this.curInt = this.interpretation;
    var nterms = this.reduceTerms(atom.terms);
    var redAtom = atom.predicate+nterms.toString();
    if (redAtom in this.curInt && thic.curInt[redAtom] != (atom==literal)) {
        return false;
    }
    this.interpretation[redAtom] = (atom==literal);
    return true;
}

Model.prototype.getDomainClauses = function() {
    res = [];
    log('creating clauses for current domain(s)');
    for (var c=0; c<this.modelfinder.clauses.length; c++) {
        var clause = this.modelfinder.clauses[c];
        var variables = [];
        for (var i=0; i<clause.length; i++) {
            variables = variables.concatNoDuplicates(this.parser.getVariables(clause[i]));
        }
        if (variables.length == 0) {
            res.push(clause);
            continue;
        }
        var interpretations = this.getVariableAssignments(variables);
        for (var i=0; i<interpretations.length; i++) {
            var interpretation = interpretations[i];
            var nclause = clause.map(function(formula) {
                var nformula = formula;
                for (var i=0; i<variables.length; i++) {
                    nformula = nformula.substitute(variables[i], interpretation[i]);
                }
                return nformula;
            });
            res.push(nclause);
        }
    }
    log('           clauses: '+res);
    res = this.modelfinder.simplifyClauses(res);
    log('simplified clauses: '+res);
    return res;
}

Model.prototype.getVariableAssignments = function(variables) {
    var res = [];
    var tuple = Array.getArrayOfZeroes(variables.length);
    res.push(tuple.copy());
    var maxValues = [];
    for (var i=0; i<variables.length; i++) {
        maxValues.push(this.parser.expressionType[variables[i]] == 'variable' ?
                       this.domain.length-1 : this.worlds.length-1);
    }
    while (Model.iterateTuple(tuple, maxValues)) { 
        res.push(tuple.copy());
    }
    return res;
}

Model.iterateTuple = function(tuple, maxValues) {
    for (var i=tuple.length-1; i>=0; i--) {
        if (tuple[i] < maxValues[i]) {
            tuple[i]++;
            return true;
        }
        tuple[i] = 0;
    }
    return false;
}

Model.prototype.simplifyRemainingClauses = function() {
    log("simplifying remaining clauses");
    log(this.clauses);
    
    var nclauses = [];
    CLAUSELOOP:
    for (var i=0; i<this.clauses.length; i++) {
        var nclause = [];
        for (var j=0; j<this.clauses[i].length; j++) {
            var literal = this.clauses[i][j];
            var atom = literal.sub || literal;
            var nterms = this.reduceTerms(atom.terms);
            var redAtomStr = atom.predicate+nterms.toString();
            if (redAtomStr in this.curInt) {
                if (this.curInt[redAtomStr] == (atom==literal)) {
                    continue CLAUSELOOP;
                }
                else { 
                    continue;
                }
            }
            var redAtom = new AtomicFormula(atom.predicate, nterms);
            if (atom==literal) nclause.push(redAtom);
            else nclause.push(new NegatedFormula(redAtom));
        }
        nclauses.push(nclause);
    }
    nclauses.sort(function(a,b) {
        return a.length > b.length;
    });
    log(nclauses);
    this.clauses = nclauses;
}

Model.prototype.copy = function() {
    var nmodel = new Model();
    nmodel.modelfinder = this.modelfinder;
    nmodel.parser = this.parser;
    nmodel.domain = this.domain;
    nmodel.worlds = this.worlds;
    nmodel.isModal = this.isModal;
    nmodel.interpretation = this.interpretation;
    nmodel.termValues = this.termValues;
    nmodel.clauses = this.clauses.copy();
    return nmodel;
}

Model.prototype.toHTML = function() {
    var str = "<table>";
    if (this.parser.isModal) {
        function w(num) {
            return 'w<sub>'+num+'</sub>';
        }
        str += "<tr><td align='right'>Worlds: </td><td align='left'>{ ";
        str += this.worlds.map(function(n){return w(n)}).join(", ");
        str += " }</td></tr>\n";
        if (!this.parser.isPropositional) {
            str += "<tr><td>Individuals: </td><td align='left'>{ ";
            str += this.domain.join(", ");
            str += " }</td></tr>\n";
        }
    }
    else if (!this.parser.isPropositional) {
        str += "<tr><td align='right'>Domain: </td><td align='left'>{ ";
        str += this.domain.join(", ");
        str += " }</td></tr>\n";
    }
    var extensions = this.getExtensions();

    for (var i=0; i<this.modelfinder.constants.length; i++) {
        var sym = this.modelfinder.constants[i];
        var ext = extensions[sym];
        var val = sym == this.parser.w ? w(ext) : ext;
        if (sym == this.parser.w) sym = '@';
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    for (var i=0; i<this.modelfinder.funcSymbols.length; i++) {
        var sym = this.modelfinder.funcSymbols[i];
        var ext = extensions[sym];
        if (ext.length > 0 && !ext[0].isArray) {
            var val = '{ '+ext.join(',')+' }';
        }
        else {
            var val = '{ '+ext.map(function(tuple) {
                return '('+tuple.join(',')+')';
            }).join(', ')+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    var isModal = this.parser.isModal;
    var R = this.parser.R;
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        var sym = this.modelfinder.predicates[i];
        var ext = extensions[sym];
        var val;
        if (!ext.isArray) { 
            val = ext;
        }
        else if (ext.length > 0 && !ext[0].isArray) {
            if (isModal) ext = ext.map(function(n){return w(n)});
            val = '{ '+ext.join(',')+' }';
        }
        else {
            val = '{ '+ext.map(function(tuple) {
                if (isModal) {
                    tuple[tuple.length-1] = w(tuple[tuple.length-1]);
                    if (sym == R) tuple[0] = w(tuple[0]);
                }
                return '('+tuple.join(',')+')';
            }).join(', ')+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }

    str += "</table>";
    return str;
}

Model.prototype.getExtensions = function() {
    var result = {};
    for (var i=0; i<this.modelfinder.constants.length; i++) {
        var cons = this.modelfinder.constants[i];
        result[cons] = this.interpretation[cons] || 0;
    }
    var interpretedStrings = Object.keys(this.interpretation);
    for (var i=0; i<this.modelfinder.funcSymbols.length; i++) {
        var f = this.modelfinder.funcSymbols[i];
        result[f] = [];
        for (var j=0; j<interpretedStrings.length; j++) {
            var expr = interpretedStrings[j];
            if (expr.indexOf('['+f+',') == 0) {
                var args = expr.slice(1,-1).split(',');
                args.shift(); 
                var val = this.interpretation[expr];
                result[f].push(args.concat([val]));
            }
        }
    }
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        var p = this.modelfinder.predicates[i];
        result[p] = (this.parser.arities[p] == 0) ? false : [];
        for (var j=0; j<interpretedStrings.length; j++) {
            var expr = interpretedStrings[j];
            if (expr.indexOf(p+'[') == 0) { 
                var val = this.interpretation[expr];
                var args = expr.substr(p.length).slice(1,-1).split(',');
                if (args[0] == '') {
                    result[p] = val;
                }
                else {
                    if (!val) continue;
                    if (args.length == 1) {
                        result[p].push(args[0]);
                    }
                    else {
                        result[p].push(args);
                    }
                }
            }
        }
    }
    return result;
}
Model.prototype.toString = function() {
    return this.toHTML().replace(/<.+?>/g, '');
}
Model.prototype.curIntToString = function() {
    var res = '';
    var keys = Object.keys(this.curInt);
    for (var i=0; i<keys.length; i++) {
        res += keys[i]+': '+this.curInt[keys[i]]+'\n';
    }
    return res;
}
