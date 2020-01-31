Array.prototype.isArray = true;
Array.prototype.toString = function() 
{
    return "["+this.join(",")+"]";
}

if (!Array.prototype.includes) 
{ 
    Array.prototype.includes = function(e) 
    {
        for (var j=0; j<this.length; j++) 
        {
            if (this[j] == e) 
            	return true;
        }
        return false;
    }
}
Array.prototype.remove = function(e) 
{
    var ix1 = this.indexOf(e);
    if (ix1 > -1) this.splice(ix1, 1);
}
Array.prototype.intersect = function(es) 
{
    for (var j=0; j<this.length; j++) 
    {
        if (es.indexOf(this[j]) == -1) 
        {
            this.splice(j--, 1);
        }
    }
}
Array.prototype.insert = function(e, ix1) 
{
     return this.splice(ix1, 0, e);
}
Array.prototype.concatNoDuplicates = function(array1) 
{
    var h1 = {};
    var r1 = [];
    for (var j=0; j<this.length; j++)
    {
        h1[this[j].toString()] = true;
        r1.push(this[j]);
    }
    for(var j=0; j<array1.length; j++)
    {
        var s = array1[j].toString();
        if (!h1[s])
        {
            h1[s] = true;
            r1.push(array1[j]);
        }
    }
    return r1;
}
Array.prototype.removeDuplicates = function() 
{
    var h1 = {};
    var r1 = [];
    for (var j=0; j<this.length; j++)
    {
        var s = this[j].toString();
        if (!h1[s]) 
        {
            h1[s] = true;
            r1.push(this[j]);
        }
    }
    return r1;
}
Array.getArrayOfZeroes = function(length) 
{
    for (var j = 0, a = new Array(length); j < length;) 
    	a[j++] = 0;
    return a;
}

Array.getArrayOfNumbers = function(length) 
{
    for (var j = 0, a = new Array(length); j < length; j++) 
    	a[j] = j;
    return a;
}
Array.prototype.copy = function() 
{
    var rs1 = [];
    for (var j=0; j<this.length; j++) 
    	rs1[j] = this[j];
    return rs1;
}
Array.prototype.copyDeep = function() 
{
    var rs1 = [];
    for (var j=0; j<this.length; j++) 
    {
        if (this[j].isArray) 
        	rs1[j] = this[j].copyDeep();
        else 
        	rs1[j] = this[j];
    }
    return rs1;
}
Array.prototype.equals = function(arr1) 
{
    if (this.length != arr1.length) 
    	return false;
    for (var j=0; j<this.length; j++) 
    {
        if (this[j].isArray) 
        {
            if (!arr1[j].isArray) 
            	return false;
            if (!this[j].equals(arr1[j])) 
            	return false;
        }
        else if (this[j] != arr1[j]) 
        	return false;
    }
    return true;
}