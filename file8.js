var fFieldValue = '';
function updateInput() {
    var os = document.forms[0].flaField.value;
    if (os == fFieldValue) {
        return true;
    }
    cposition = this.selectionStart;
    fFieldValue = SymbolRender(os);  
    var difference = os.length - fFieldValue.length
    document.forms[0].flaField.value = fFieldValue;
    this.selectionEnd = cposition - difference;
    AccessRowToggle();
}

function SymbolRender(str) {
    str = str.replace('&', '∧');
    str = str.replace('^', '∧');
    str = str.replace('<->', '↔');
    str = str.replace('->', '→');
    str = str.replace('~', '¬');
    str = str.replace(' v ', ' ∨ '); 
    str = str.replace('[]', '□');
    str = str.replace('<>', '◇');
    str = str.replace(/\(A([s-z])\)/, '∀$1'); 
    str = str.replace(/\(E([s-z])\)/, '∃$1'); 
    str = str.replace(/(?:^|\W)\(([s-z])\)/, '∀$1'); 
    str = str.replace(/\\forall[\{ ]?\}?/g, '∀');
    str = str.replace(/\\exists[\{ ]?\}?/g, '∃');
    str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, '¬');
    str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, '∨');
    str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, '∧');
    str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, '→');
    str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, '↔');
    str = str.replace(/\\[Bb]ox[\{ ]?\}?/g, '□');
    str = str.replace(/\\[Dd]iamond[\{ ]?\}?/g, '◇');
    return str;
}

function AccessRowToggle() {
    if (/[□◇]/.test(document.forms[0].flaField.value)) {
        document.getElementById('accessibilitySpan').style.display = 'inline-block';
    }
    else {
        document.getElementById('accessibilitySpan').style.display = 'none';
    }
}
document.forms[0].flaField.insertAtCaret = function(str) {
   if (document.selection) {
      this.focus();
      sel = document.selection.createRange();
      sel.text = str;
      this.focus();
   }
   else if (this.selectionStart || this.selectionStart === 0) {
      
      var StartPosition = this.selectionStart;
      var EndPosition = this.selectionEnd;
      var TopScroll = this.TopScroll;
      var val = this.value; 
      this.value = val.substring(0, StartPosition)+str+val.substring(EndPosition,val.length);
      this.focus();
      this.selectionStart = StartPosition + str.length;
      this.selectionEnd = StartPosition + str.length;
      this.TopScroll = TopScroll;
   } 
   else {
      this.value += str;
      this.focus();
   }
}

document.querySelectorAll('.symbutton').forEach(function(el) {
    el.onclick = function(e) {
        var field = document.forms[0].flaField;
        var cmd = this.innerHTML;
        field.insertAtCaret(cmd);
        AccessRowToggle();
    }
});

var prover = null;
function Proof_Start() {
    var input = document.forms[0].flaField.value;
    var parser = new Parser();
    try {
        var Input_Parsed = parser.parseInput(input);
        var premises = Input_Parsed[0];
        var conclusion = Input_Parsed[1];
        var initFormulas = premises.concat([conclusion.negate()]);
    }
    catch (e) {
        alert(e);
        return false;
    }
    document.getElementById("intro").style.display = "none";
    document.getElementById("model").style.display = "none";
    document.getElementById("rootAnchor").style.display = "none";
    document.getElementById("backtostartpage").style.display = "block";
    document.getElementById("status").style.display = "block";
    document.getElementById("status").innerHTML = "<div id='working'>working</div>";
    var Access_Constraints = [];
    if (parser.isModal) {
        document.querySelectorAll('.accCheckbox').forEach(function(el) {
            if (el.checked) {
                Access_Constraints.push(el.id);
            }
        });
    }
    prover = new Prover(initFormulas, parser, Access_Constraints);
    prover.onfinished = function(treeClosed) {
        var Span_conclusion = "<span class='formula'>"+conclusion+"</span>";
        if (initFormulas.length == 1) {
            var summary = Span_conclusion + " is " + (treeClosed ? "a tautology." : "not a tautology.");
        }
        else {
            var summary = premises.map(function(f){
                return "<span class='formula'>"+f+"</span>";
            }).join(', ') + (treeClosed ? " entails " : " does not entail ") + Span_conclusion + ".";
        }
        document.getElementById("status").innerHTML = summary;
        var sentree = new SenTree(this.tree, parser); 
        if (!treeClosed) {
            if (this.counterModel) {
                }
            return; 
        }
        if (parser.isModal) {
            sentree.modalize();
        }
        document.getElementById("rootAnchor").style.display = "block";
        self.painter = new TreePainter(sentree, document.getElementById("rootAnchor"));
        self.painter.paintTree();
    }
    setTimeout(function(){
        prover.start();
    }, 1);
    return false;
}   
onload = function(e) {
    updateInput();
    document.forms[0].flaField.onkeyup = updateInput;
    document.forms[0].onsubmit = function(e) {
        setHash();
        Proof_Start();
        return false;
    }
    if (location.hash.length > 0) {
        Change_Hash();
    }
}

var Hash_Script = false;
function setHash() {
    Hash_Script = true;
    var hash = document.forms[0].flaField.value;
    var Access_Constraints = [];
    document.querySelectorAll('.accCheckbox').forEach(function(el) {
        if (el.checked) {
            Access_Constraints.push(el.id);
        }
    });
    if (Access_Constraints.length > 0) {
        hash += '||'+Access_Constraints.join('|');
    }
    location.hash = hash;
}

window.onChange_Hash = Change_Hash;

function Change_Hash() {
    if (Hash_Script) {
        Hash_Script = false;
        return;
    }
    if (prover) prover.stop();
    if (location.hash.length == 0) {
        document.getElementById("intro").style.display = "block";
        document.getElementById("model").style.display = "none";
        document.getElementById("rootAnchor").style.display = "none";
        document.getElementById("backtostartpage").style.display = "none";
        document.getElementById("status").style.display = "none";
    }
    else {
        var hash = decodeURIComponent(location.hash.substr(1).replace(/\+/g, '%20'));
        var hashparts = hash.split('||');
        document.forms[0].flaField.value = hashparts[0];
        var Access_Constraints = hashparts[1] ? hashparts[1].split('|') : [];
        document.querySelectorAll('.accCheckbox').forEach(function(el) {
            el.checked = Access_Constraints.includes(el.id); 
        });
        AccessRowToggle();
        Proof_Start();
    }
}

