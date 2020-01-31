function Prover(initFormulas, parser, accessibilityConstraints) {

    log("*** initializing prover");
    this.initFormulas = initFormulas; 
    this.parser = parser.copy();
    this.accessibilityRules = [];
    if (parser.isModal) {
        this.initFormulasNonModal = [];
        for (var i=0; i<initFormulas.length; i++) {
            this.initFormulasNonModal.push(this.parser.translateFromModal(initFormulas[i]));
        }
        if (accessibilityConstraints) {
            this.s5 = accessibilityConstraints.includes('universality');
            if (!this.s5) {
                this.accessibilityRules = accessibilityConstraints.map(function(s) {
                    return Prover[s];
                });
            }
        }
    }
    else {
        this.initFormulasNonModal = initFormulas;
    }
    this.initFormulasNormalized = this.initFormulasNonModal.map(function(f){
        return f.normalize();
    });
    log('normalized initFormulas: '+this.initFormulasNormalized);
    this.pauseLength = 10; 
    log('increasing pauseLength to '+(this.pauseLength = 100));
    this.computationLength = 20; 
    this.step = 0; 
    this.depthLimit = 2; 
    this.tree = new Tree(this);
    this.alternatives = []; 
    var mfParser = this.parser.copy();
    if (accessibilityConstraints) {
        var name_to_fla = {
            "universality": "∀v∀uRvu",
            "reflexivity": "∀vRvv",
            "symmetry": "∀v∀u(Rvu→Ruv)",
            "transitivity": "∀v∀u∀t(Rvu→(Rut→Rvt))",
            "euclidity": "∀v∀u∀t(Rvu→(Rvt→Rut))",
            "seriality": "∀v∃uRvu"
        };
        var accessibilityFormluas = accessibilityConstraints.map(function(s) {
            return mfParser.parseAccessibilityFormula(name_to_fla[s]).normalize();
        });
        this.modelfinder = new ModelFinder(
            this.initFormulasNormalized,
            mfParser,
            accessibilityFormluas,
            this.s5
        );
    }
    else {
        this.modelfinder = new ModelFinder(this.initFormulasNormalized, mfParser);
    }
    this.counterModel = null;

    this.start = function() {
        this.lastBreakTime = performance.now();
        this.nextStep();
    };

    this.stop = function() {
        this.stopTimeout = true;
    };

    this.onfinished = function() {};
    
    this.status = function() {};

}

Prover.prototype.nextStep = function() {
    this.step++;
    log('*** prover step '+this.step);
    
    log(this.tree.openBranches[0].todoList);
    var todo = this.tree.openBranches[0].todoList.shift();
    if (todo) {
        var nextRule = todo.shift();
        var args = todo;
        nextRule(this.tree.openBranches[0], args);
        log(this.tree);

        if (this.tree.openBranches.length == 0) {
            log('tree closed');
            return this.onfinished(1);
        }

        if (this.tree.openBranches[0].nodes.length > this.depthLimit * 4) {
            log('reached complexity limit for backtracking');
            this.limitReached();
        }
    } 
    if (this.modelfinder.nextStep()) {
        this.counterModel = this.modelfinder.model;
        return this.onfinished(0);
    }
    
    if (this.step % 1000 == 999) {
        
        log("trying with increased depth for a few steps");
        this.depthLimit++;
        this.decreaseLimit = this.step + 200;
    }
    else if (this.step == this.decreaseLimit) {
        log("resetting depth");
        this.depthLimit--;
    }
    
    log((this.step == 10000 && (this.stopTimeout=true) && 'proof halted') || '');
    var timeSinceBreak = performance.now() - this.lastBreakTime;
    if (this.stopTimeout) {
        
        this.stopTimeout = false;
    }
    else if (this.pauseLength && timeSinceBreak > this.computationLength) {
        
        setTimeout(function(){
            this.lastBreakTime = performance.now();
            this.nextStep();
        }.bind(this), this.pauseLength*this.tree.numNodes/100);
    }
    else {
        this.nextStep();
    }
}

Prover.prototype.limitReached = function() {
    if (this.alternatives.length) {
        log(" * limit reached, trying stored alternative * ");
        log(this.alternatives.length+' alternatives');
        this.tree = this.alternatives.pop();
        log(this.tree);
    }
    else {
        this.depthLimit++;
        log("----- increasing depthLimit to " + this.depthLimit + " -----");
        
    }
}


Prover.alpha = function(branch, nodeList) {
    log('alpha '+nodeList[0]);
    var node = nodeList[0];
    var subnode1 = new Node(node.formula.sub1, Prover.alpha, nodeList);
    var subnode2 = new Node(node.formula.sub2, Prover.alpha, nodeList);
    branch.addNode(subnode1);
    branch.addNode(subnode2);
    branch.tryClose(subnode1);
    if (!branch.closed) branch.tryClose(subnode2);
}
Prover.alpha.priority = 1;
Prover.alpha.toString = function() { return 'alpha' }

Prover.beta = function(branch, nodeList) {
    log('beta '+nodeList[0]);
    var node = nodeList[0];
    branch.tree.openBranches.unshift(branch.copy());
    var subnode1 = new Node(node.formula.sub1, Prover.beta, nodeList);
    var subnode2 = new Node(node.formula.sub2, Prover.beta, nodeList);
    branch.tree.openBranches[0].addNode(subnode2);
    branch.addNode(subnode1);
    branch.tryClose(subnode1);
    branch.tree.openBranches[0].tryClose(subnode2);
}
Prover.beta.priority = 9;
Prover.beta.toString = function() { return 'beta' }

Prover.gamma = function(branch, nodeList, matrix) {
    log('gamma '+nodeList[0]);
    var node = nodeList[0];
    if (branch.freeVariables.length == this.depthLimit) {
        log("depthLimit " + this.depthLimit + " exceeded!");
        this.limitReached();
        return null;
    }
    
    if (!matrix) branch.todoList.push([Prover.gamma, node]);
    var newVariable = branch.newVariable(matrix);
    var matrix = matrix || node.formula.matrix;
    var newFormula = matrix.substitute(node.formula.variable, newVariable);
    var newNode = new Node(newFormula, Prover.gamma, nodeList); 
    newNode.instanceTerm = newVariable; 
    branch.addNode(newNode);
    branch.tryClose(newNode);
}
Prover.gamma.priority = 7;
Prover.gamma.toString = function() { return 'gamma' }

Prover.modalGamma = function(branch, nodeList) {
    log('modalGamma '+nodeList[0]);
    var node = nodeList[0];
    branch.todoList.push([Prover.modalGamma, node]);
    
    if (branch.tree.prover.s5) {
        return Prover.gamma(branch, nodeList, node.formula.matrix.sub2);
    }

    var wRx = node.formula.matrix.sub1.sub;
    log('looking for '+wRx.predicate+wRx.terms[0]+'* nodes');
    OUTERLOOP:
    for (var i=0; i<branch.literals.length; i++) {
        var wRy = branch.literals[i].formula;
        if (wRy.predicate == wRx.predicate && wRy.terms[0] == wRx.terms[0]) {
            log('found '+wRy);
            for (var j=0; j<branch.nodes.length; j++) {
                if (branch.nodes[j].fromRule == Prover.modalGamma &&
                    branch.nodes[j].fromNodes[0] == node &&
                    branch.nodes[j].fromNodes[1] == branch.literals[i]) {
                    log('already used');
                    continue OUTERLOOP;
                }
            }
            var modalMatrix = node.formula.matrix.sub2;
            var v = wRy.terms[1];
            log('expanding: '+node.formula.variable+' => '+v);
            var newFormula = modalMatrix.substitute(node.formula.variable, v);
            var newNode = new Node(newFormula, Prover.modalGamma, [node, branch.literals[i]]);
            newNode.instanceTerm = v;
            if (branch.addNode(newNode)) {
                branch.tryClose(newNode);
                break;
            }
        }
    }
}
Prover.modalGamma.priority = 8;
Prover.modalGamma.toString = function() { return 'modalGamma' }
    
Prover.delta = function(branch, nodeList, matrix) {
    log('delta '+nodeList[0]);
    var node = nodeList[0];
    var fla = node.formula;
    var funcSymbol = branch.newFunctionSymbol(matrix);
    if (branch.freeVariables.length > 0) {
        if (branch.tree.prover.s5) {
            var skolemTerm = branch.freeVariables.filter(function(v) {
                return v[0] == (matrix ? 'ζ' : 'ξ');
            });
        }
        else {
            var skolemTerm = branch.freeVariables.copy();
        }
        skolemTerm.unshift(funcSymbol);
    }
    else {
        var skolemTerm = funcSymbol;
    }
    var matrix = matrix || node.formula.matrix;
    var newFormula = matrix.substitute(node.formula.variable, skolemTerm);
    var newNode = new Node(newFormula, Prover.delta, nodeList);
    newNode.instanceTerm = skolemTerm;
    branch.addNode(newNode);
    branch.tryClose(newNode);
}
Prover.delta.priority = 2;
Prover.delta.toString = function() { return 'delta' }

Prover.modalDelta = function(branch, nodeList) {
    log('modalDelta '+nodeList[0]);
    var node = nodeList[0]; 
    if (branch.tree.prover.s5) {
        return Prover.delta(branch, nodeList, node.formula.matrix.sub2);
    }
    var fla = node.formula;
    var newWorldName = branch.newWorldName();
    var fla1 = node.formula.matrix.sub1.substitute(node.formula.variable, newWorldName);
    var fla2 = node.formula.matrix.sub2.substitute(node.formula.variable, newWorldName);
    var newNode1 = new Node(fla1, Prover.modalDelta, nodeList); 
    var newNode2 = new Node(fla2, Prover.modalDelta, nodeList); 
    newNode2.instanceTerm = newWorldName;
    branch.addNode(newNode1);
    branch.addNode(newNode2);
    branch.tryClose(newNode2);
}
Prover.modalDelta.priority = 2;
Prover.modalDelta.toString = function() { return 'modalDelta' }

Prover.reflexivity = function(branch, nodeList) {
    log('applying reflexivity rule');
    if (nodeList.length == 0) {
        var worldName = branch.tree.parser.w;
    }
    else {
        var worldName = nodeList[0].formula.terms[1];
    }
    var R = branch.tree.parser.R;
    var formula = new AtomicFormula(R, [worldName, worldName]);
    log('adding '+formula);
    var newNode = new Node(formula, Prover.reflexivity, nodeList || []);
    branch.addNode(newNode);
}
Prover.reflexivity.priority = 3;
Prover.reflexivity.needsPremise = false; 
Prover.reflexivity.premiseCanBeReflexive = false; 
Prover.reflexivity.toString = function() { return 'reflexivity' }

Prover.symmetry = function(branch, nodeList) {
    log('applying symmetry rule');
    var nodeFormula = nodeList[0].formula;
    var R = branch.tree.parser.R;
    var formula = new AtomicFormula(R, [nodeFormula.terms[1], nodeFormula.terms[0]]);
    log('adding '+formula);
    var newNode = new Node(formula, Prover.symmetry, nodeList);
    branch.addNode(newNode);
}
Prover.symmetry.priority = 3;
Prover.symmetry.needsPremise = true; 
Prover.symmetry.premiseCanBeReflexive = false; 
Prover.symmetry.toString = function() { return 'symmetry' }

Prover.euclidity = function(branch, nodeList) {
    log('applying euclidity rule');
    var node = nodeList[0];
    var nodeFla = node.formula;
    var flaStrings = branch.nodes.map(function(n) {
        return n.formula.string;
    });
    var R = branch.tree.parser.R;
    for (var i=0; i<branch.nodes.length; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate != R) continue;
        if (earlierFla.terms[0] == nodeFla.terms[0]) {
            var newFla;
            if (!flaStrings.includes(R + earlierFla.terms[1] + nodeFla.terms[1])) {
                newFla = new AtomicFormula(R, [earlierFla.terms[1], nodeFla.terms[1]]);
            }
            else if (!flaStrings.includes(R + nodeFla.terms[1] + earlierFla.terms[1])) {
                newFla = new AtomicFormula(R, [nodeFla.terms[1], earlierFla.terms[1]]);
            }
            if (newFla) {
                log('adding '+newFla);
                var newNode = new Node(newFla, Prover.euclidity, [branch.nodes[i], node]);
                if (branch.addNode(newNode)) {
                    branch.todoList.unshift([Prover.euclidity, node]);
                    return;
                }
            }
        }
        if (branch.nodes[i] == node) break;
    }
}
Prover.euclidity.priority = 3;
Prover.euclidity.needsPremise = true;
Prover.euclidity.premiseCanBeReflexive = false; 
Prover.euclidity.toString = function() { return 'euclidity' }

Prover.transitivity = function(branch, nodeList) {
    log('applying transitivity rule');
    var R = branch.tree.parser.R;
    var node = nodeList[0];
    var nodeFla = node.formula;
    for (var i=0; i<branch.nodes.length; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate != R) continue;
        var newFla = null;
        if (earlierFla.terms[1] == nodeFla.terms[0]) {
            newFla = new AtomicFormula(R, [earlierFla.terms[0], nodeFla.terms[1]]);
        }
        else if (earlierFla.terms[0] == nodeFla.terms[1]) {
            newFla = new AtomicFormula(R, [nodeFla.terms[0], earlierFla.terms[1]]);
        }
        if (newFla) {
            log('matches '+earlierFla+': adding '+newFla);
            var newNode = new Node(newFla, Prover.transitivity, [branch.nodes[i], node]);
            if (branch.addNode(newNode)) {
                branch.todoList.unshift([Prover.transitivity, node]);
                return;
            }
        }
        if (branch.nodes[i] == node) break;
    }
}
Prover.transitivity.priority = 3;
Prover.transitivity.needsPremise = true; 
Prover.transitivity.premiseCanBeReflexive = false; 
Prover.transitivity.toString = function() { return 'transitivity' }

Prover.seriality = function(branch, nodeList) {
    log('applying seriality rule');
    var R = branch.tree.parser.R;
    if (nodeList.length == 0) {
        var oldWorld = branch.tree.parser.w;
    }
    else {
        var oldWorld = nodeList[0].formula.terms[1];
    } 
    for (var i=0; i<branch.nodes.length-1; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate == R && earlierFla.terms[0] == oldWorld) {
            log(oldWorld+' can already see a world');
            return;
        }
    }
    var newWorld = branch.newWorldName();
    var newFla = new AtomicFormula(R, [oldWorld, newWorld]);
    log('adding '+newFla);
    var newNode = new Node(newFla, Prover.seriality, []);
    branch.addNode(newNode);
}
Prover.seriality.priority = 10;
Prover.seriality.needsPremise = false;
Prover.seriality.premiseCanBeReflexive = false; 
Prover.seriality.toString = function() { return 'seriality' }


function Tree(prover) {
    if (!prover) return; 
    this.prover = prover;
    this.parser = prover.parser;
    var initBranch = new Branch(this);
    for (var i=0; i<prover.initFormulasNormalized.length; i++) {
        var formula = prover.initFormulasNormalized[i];
        var node = new Node(formula);
        initBranch.addNode(node);
    }
    this.openBranches = [initBranch];
    this.closedBranches = [];
    this.numNodes = 0;
}

Tree.prototype.closeBranch = function(branch, complementary1, complementary2) {
    branch.closed = true;
    this.markUsedNodes(branch, complementary1, complementary2);
    this.pruneBranch(branch, complementary1, complementary2);
    this.openBranches.remove(branch);
    this.closedBranches.push(branch);
    this.pruneAlternatives();
}

Tree.prototype.pruneAlternatives = function() {
    var alternatives = this.prover.alternatives.copy();
    ALTLOOP:
    for (var i=0; i<alternatives.length; i++) {
        var altTree = alternatives[i];
        for (var j=0; j<this.openBranches.length; j++) {
            var openBranch = this.openBranches[j];
            if (!altTree.containsOpenBranch(openBranch)) {
                continue ALTLOOP
            }
        }
        log('alternative '+i+' contains all open branch of this tree; removing');
        this.prover.alternatives.remove(altTree);
    }
}

Tree.prototype.containsOpenBranch = function(branch) {
    BRANCHLOOP:
    for (var i=0; i<this.openBranches.length; i++) {
        var oBranch = this.openBranches[i];
        if (branch.nodes.length != oBranch.nodes.length) continue;
        for (var j=1; j<branch.nodes.length; j++) {
            if (branch.nodes[j].formula.string != oBranch.nodes[j].formula.string) {
                continue BRANCHLOOP;
            }
        }
        return true;
    }
    return false;
}

Tree.prototype.markUsedNodes = function(branch, complementary1, complementary2) {
    var ancestors = [complementary1, complementary2];
    var n;
    while ((n = ancestors.shift())) {
        if (!n.used) {
            for (var i=0; i<n.fromNodes.length; i++) {
                ancestors.push(n.fromNodes[i]);
            }
            n.used = true;
        }
    }
}


Tree.prototype.pruneBranch = function(branch, complementary1, complementary2) {
    var obranches = this.openBranches.concat(this.closedBranches);
    obranches.remove(branch);
    for (var i=branch.nodes.length-1; i>0; i--) {
        for (var j=0; j<obranches.length; j++) {
            if (obranches[j].nodes[i] &&
                obranches[j].nodes[i] != branch.nodes[i] &&
                obranches[j].nodes[i].expansionStep == branch.nodes[i].expansionStep) {
                if (branch.nodes[i].used) {
                    // quit if sibling branch is open:
                    if (!obranches[j].closed) return;
                }
                else {
                    log("pruning branch "+obranches[j]+": unused expansion of "+branch.nodes[i].fromNodes[0]);
                    if (obranches[j].closed) {
                        this.closedBranches.remove(obranches[j]);
                        branch.nodes[i].fromNodes[0].used = false;
                    }
                    else {
                        this.openBranches.remove(obranches[j]);
                    }
        
                }
            }
        }
    }
}

Tree.prototype.closeCloseableBranches = function() {
    var openBranches = this.openBranches.copy();
    for (var k=0; k<openBranches.length; k++) {
        var branch = openBranches[k];
        BRANCHLOOP:
        for (var i=branch.nodes.length-1; i>=0; i--) {
            var n1 = branch.nodes[i];
            var n1negated = (n1.formula.operator == '¬');
            var closed = false;
            for (var j=i-1; j>=0; j--) {
                var n2 = branch.nodes[j];
                if (n2.formula.operator == '¬') {
                    if (n2.formula.sub.equals(n1.formula)) closed = true;
                }
                else if (n1negated) {
                    if (n1.formula.sub.equals(n2.formula)) closed = true;
                }
                if (closed) {
                    this.closeBranch(branch, n1, n2);
                    log("+++ branch closed +++");
                    break BRANCHLOOP;
                }
            }
        }
    }
}

Tree.prototype.copy = function() {
    var ntree = new Tree();
    var nodemap = {} 
    ntree.prover = this.prover;
    ntree.parser = this.parser;
    ntree.numNodes = this.numNodes;
    ntree.openBranches = [];
    for (var i=0; i<this.openBranches.length; i++) {
        ntree.openBranches.push(copyBranch(this.openBranches[i]));
    }
    ntree.closedBranches = [];
    for (var i=0; i<this.closedBranches.length; i++) {
        ntree.closedBranches.push(copyBranch(this.closedBranches[i]));
    }
    return ntree;
    
    function copyBranch(orig) {
        var nodes = [];
        var literals = [];
        var todoList = [];
        for (var i=0; i<orig.nodes.length; i++) {
            nodes.push(copyNode(orig.nodes[i]));
        } 
        for (var i=0; i<orig.literals.length; i++) {
            literals.push(nodemap[orig.literals[i].id]);
        }
        for (var i=0; i<orig.todoList.length; i++) {
            var todo = [orig.todoList[i][0]];
            for (var j=1; j<orig.todoList[i].length; j++) {
                todo.push(nodemap[orig.todoList[i][j].id]);
            }
            todoList.push(todo);
        } 
        var b = new Branch(ntree, nodes, literals,
                           orig.freeVariables.copy(),
                           orig.skolemSymbols.copy(),
                           todoList, orig.closed);
        b.id = orig.id;
        return b;
    }
    
    function copyNode(orig) {
        if (nodemap[orig.id]) return nodemap[orig.id];
        var n = new Node();
        n.formula = orig.formula;
        n.fromRule = orig.fromRule;
        n.fromNodes = [];
        for (var i=0; i<orig.fromNodes.length; i++) {
            n.fromNodes.push(nodemap[orig.fromNodes[i].id]);
        }
        n.type = orig.type;
        n.expansionStep = orig.expansionStep;
        n.used = orig.used;
        n.id = orig.id;
        n.instanceTerm = orig.instanceTerm;
        nodemap[orig.id] = n;
        return n;
    }
    
}

Tree.prototype.applySubstitution = function(sub) {
    var branches = this.openBranches.concat(this.closedBranches);
    for (var i=0; i<sub.length; i+=2) {
        var nodeProcessed = {};
        for (var b=0; b<branches.length; b++) {
            for (var n=branches[b].nodes.length-1; n>=0; n--) {
                var node = branches[b].nodes[n]; 
                if (nodeProcessed[node.id]) break;
                nodeProcessed[node.id] = true;                    
                node.formula = node.formula.substitute(sub[i], sub[i+1]);
                if (node.instanceTerm) {
                    node.instanceTerm = AtomicFormula.substituteInTerm(node.instanceTerm, sub[i], sub[i+1]);
                }
            }
            branches[b].freeVariables.remove(sub[i]);
        }
    }
}

Tree.prototype.toString = function() {
    for (var i=0; i<this.closedBranches.length; i++) {
        this.closedBranches[i].nodes[this.closedBranches[i].nodes.length-1].__markClosed = true;
    }
    var branches = this.closedBranches.concat(this.openBranches);
    var res = "<table><tr><td align='center' style='font-family:monospace'>" +
        getTree(branches[0].nodes[0])+"</td</tr></table>";
    for (var i=0; i<this.closedBranches.length; i++) {
        delete this.closedBranches[i].nodes[this.closedBranches[i].nodes.length-1].__markClosed;
    }
    return res;
    
    function getTree(node) { 
        var recursionDepth = arguments[1] || 0;
        if (++recursionDepth > 100) return "<b>...<br>[max recursion]</b>";
        var children = [];
        for (var i=0; i<branches.length; i++) {
            for (var j=0; j<branches[i].nodes.length; j++) {
                if (branches[i].nodes[j-1] != node) continue;
                if (!children.includes(branches[i].nodes[j])) {
                    children.push(branches[i].nodes[j]);
                }
            }
        }
        var res = (node.used ? '.' : '') + node + (node.__markClosed ? "<br>x<br>" : "<br>");
        if (children[1]) {
            var tdStyle = "font-family:monospace; border-top:1px solid #999; padding:3px; border-right:1px solid #999";
            var td = "<td align='center' valign='top' style='" + tdStyle + "'>"; 
            res += "<table><tr>"+ td + getTree(children[0], recursionDepth) +"</td>\n"
                + td + getTree(children[1], recursionDepth) + "</td>\n</tr></table>";
        }
        else if (children[0]) res += getTree(children[0], recursionDepth);
        return res;
    }
}

function Branch(tree, nodes, literals, freeVariables, skolemSymbols, todoList, closed) {
    this.tree = tree;
    this.nodes = nodes || [];
    this.literals = literals || [];
    this.freeVariables = freeVariables || [];
    this.skolemSymbols = skolemSymbols || [];
    this.todoList = todoList || [];
    this.closed = closed || false;
    this.id = Branch.counter++;
}
Branch.counter = 0;

Branch.prototype.newVariable = function(isWorldTerm) {
    var sym = isWorldTerm ? 'ζ' : 'ξ';
    var res = sym+'1';
    for (var i=this.freeVariables.length-1; i>=0; i--) {
        if (this.freeVariables[i][0] == sym) {
            res = sym+(this.freeVariables[i].substr(1)*1+1);
            break;
        }
    }
    this.freeVariables.push(res);
    return res;
}

Branch.prototype.newFunctionSymbol = function(isWorldTerm) {
    var sym = isWorldTerm ? 'ω' : 'φ';
    var res = sym+'1';
    for (var i=this.skolemSymbols.length-1; i>=0; i--) {
        if (this.skolemSymbols[i][0] == sym) {
            res = sym+(this.skolemSymbols[i].substr(1)*1+1);
            break;
        }
    }
    this.skolemSymbols.push(res);
    return res;
}

Branch.prototype.newWorldName = function() {
    return this.newFunctionSymbol(true);
}

Branch.prototype.tryClose = function(node) {
    
    log('checking if branch can be closed with '+node);
    var negatedFormula = (node.formula.operator == '¬') ? node.formula.sub : node.formula.negate();
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].formula.equals(negatedFormula)) {
            this.tree.closeBranch(this, node, this.nodes[i]);
            log("+++ branch closed +++");
            return true;
        }
    }
    
    if (node.type != 'literal') return false; 
    var unifiers = []; 
    var otherNodes = []; 
    for (var i=this.literals.length-1; i>=0; i--) {
        if (this.literals[i] == node) continue;
        var u = negatedFormula.unify(this.literals[i].formula);
        if (u.isArray) {
            var isNew = true;
            for (var j=0; j<unifiers.length; j++) {
                if (unifiers[j].equals(u)) isNew = false;
            }
            if (isNew) {
                unifiers.push(u);
                otherNodes.push(this.literals[i]); 
            }
        }
    }
    if (unifiers.length == 0) {
        return false;
    }
   
    var considerAlternatives = false;
    var unifier = unifiers[0], otherNode = otherNodes[0];
    VARLOOP: 
    for (var i=0; i<unifier.length; i+=2) {
        var variable = unifier[i];
        for (var j=0; j<this.tree.openBranches.length; j++) {
            var branch = this.tree.openBranches[j];
            if (branch != this && branch.freeVariables.includes(variable)) {
                considerAlternatives = true;
                break VARLOOP;
            }
        }
    }
    if (considerAlternatives) {
        for (var i=1; i<unifiers.length; i++) {
            var altTree = this.tree.copy();
            log("processing and storing alternative unifier for "+node+": "+unifiers[i]);
            altTree.applySubstitution(unifiers[i]);
            altTree.closeCloseableBranches();
            log('alternative tree:\n'+altTree);
            if (altTree.openBranches.length == 0) {
                log('alternative tree closes, stopping proof');
                this.tree.prover.tree = altTree;
                return true;
            }
            this.tree.prover.alternatives.push(altTree);
        }
        if (this.todoList.length) {
            var altTree = this.tree.copy();
            log("storing non-unified alternative"); 
            this.tree.prover.alternatives.push(altTree);
        }
        log(this.tree.prover.alternatives.length+' alternatives');
    }
    else {
        log("no need to consider alternatives for backtracking");
    }
    log("applying unifier for "+node+" and "+otherNode+": "+unifier);
    this.tree.applySubstitution(unifier);
    this.tree.closeBranch(this, node, otherNode);
    log(this.tree);
    log("+++ branch closed +++");
    return true;
}

Branch.prototype.copy = function() {
    return new Branch(this.tree,
                      this.nodes.copy(), 
                      this.literals.copy(),
                      this.freeVariables.copy(),
                      this.skolemSymbols.copy(),
                      this.todoList.copyDeep(), 
                      this.closed);
}


Branch.prototype.addNode = function(node) {
    var addToTodo = true;
    if (this.containsFormula(node.formula)) {
        if (node.fromRule == Prover.alpha || node.fromRule == Prover.beta) {
            addToTodo = false;
        }
        else {
            return null;
        }
    }
    this.nodes.push(node);
    this.tree.numNodes++;
    if (node.type == 'literal') {
        this.literals.push(node);
    }
    if (!this.closed && addToTodo) {
        this.expandTodoList(node);
    }
    node.expansionStep = this.tree.prover.step;
    return node;
}

Branch.prototype.containsFormula = function(formula) {
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].formula.string == formula.string) return true;
    }
    return false;
}

Branch.prototype.expandTodoList = function(node) {
    if (node.type != 'literal') {
        var expansionRule = node.getExpansionRule();
	for (var i=0; i<this.todoList.length; i++) {
	    if (expansionRule.priority <= this.todoList[i][0].priority) break;
	}
	this.todoList.insert([expansionRule, node], i);
    }
    if (this.tree.parser.isModal) {
        if (this.nodes.length == 1) {
            this.addAccessibilityRuleApplications();
        }
        else if (node.formula.predicate == this.tree.parser.R) {
            this.addAccessibilityRuleApplications(node);
        }
    }
}

Branch.prototype.addAccessibilityRuleApplications = function(node) {
    
    for (var i=0; i<this.tree.prover.accessibilityRules.length; i++) {
        var rule = this.tree.prover.accessibilityRules[i];
        for (var j=0; j<this.todoList.length; j++) {
            if (rule.priority <= this.todoList[j][0].priority) break;
        }
        if (node) {
            if (node.formula.terms[0] != node.formula.terms[1] || rule.premiseCanBeReflexive) {
                this.todoList.insert([rule, node], j);
            }
        }
        else {
            if (!rule.needsPremise) {
                this.todoList.insert([rule], j);
            }
        }
    }
}

Branch.prototype.toString = function() {
    return this.nodes.map(function(n){ return n.formula.string }).join(',');
}


function Node(formula, fromRule, fromNodes) {
    if (!formula) return;
    this.formula = formula;
    this.fromRule = fromRule || null;
    this.fromNodes = fromNodes || [];
    this.type = formula.type;
    this.id = Node.counter++;
}
Node.counter = 0;

Node.prototype.getExpansionRule = function() {
    return Prover[this.type];
}

Node.prototype.toString = function() {
    return this.formula.string;
}
