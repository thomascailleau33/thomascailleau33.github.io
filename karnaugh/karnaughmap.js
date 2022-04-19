// Copyright (C) Thorsten Thormaehlen, Marburg, 2013, All rights reserved
// Contact: www.thormae.de

// This software is written for educational (non-commercial) purpose. 
// There is no warranty or other guarantee of fitness for this software, 
// it is provided solely "as is". 

function UIElement(x, y, width, height, type, ref, subref, slotType) {
  this.x = x;
  this.y = y;
  this.x2 = x + width;
  this.y2 = y + height;
  this.type = type; // 0 = field, 1 = slot, 2 connection
  this.ref = ref;
}

function KVField() {
  this.position = [0.0, 0.0];
  this.value = 0;
  this.active = false;
  this.uniqueID = -1;
  this.truthmapID = -1;
}

function KVBlock() {
  this.fieldID = -1;
  this.dimx = -1;
  this.dimy = -1;
  this.used = false;
  this.color = [0, 0, 0];
  this.primTerm = "";
}

function KarnaughMapDataCtrl(qmcRef) {
  this.noOfVars = -1;
  this.fieldLines = -1;
  this.fieldPerLine = -1;
  this.fieldBorder = -1;
  this.fieldHeight = 40;
  this.fieldWidth = 40;
  this.qmc = qmcRef;
  this.fields = new Array();
  this.blocks = new Array();
  this.allowDontCare = false;
  
  this.init = function(no) {

    this.noOfVars = no;

    this.qmc.setNoOfVars(no);

    var noOfEvenVars = Math.floor(this.noOfVars / 2);
    var noOfOddVars = Math.floor((this.noOfVars + 1) / 2);

    this.fieldLines = Math.pow(2, noOfEvenVars);
    this.fieldPerLine = Math.pow(2, noOfOddVars);
    this.fieldBorder = noOfOddVars * 20;

    this.fields.length = 0;
    this.blocks.length = 0;

    var id = 0;
    for (var i = 0; i < this.fieldLines; i++) {
      for (var j = 0; j < this.fieldPerLine; j++) {
        var field = new KVField();
        field.position[0] = this.fieldBorder + j * this.fieldWidth;
        field.position[1] = this.fieldBorder + i * this.fieldHeight;
        field.value = 0;
        field.uniqueID = id;
        this.fields.push(field);
        id++;
      }
    }

    var mapped = 0;
    this.fields[0].truthmapID = 0;
    this.fields[1].truthmapID = 1;
    var mirrorDirection = 0;
    var mirrorXCount = 2;
    var mirrorYCount = 1;
    var mapped = 2;
    var x = 0;
    var y = 1;
    var loop = 0;
    var direction = 0;
    while (loop < this.noOfVars - 1) {
      for (var xx = 0; xx < mirrorXCount; xx++) {
        for (var yy = 0; yy < mirrorYCount; yy++) {
          var loc = xx + yy * this.fieldPerLine;

          if (direction === 0) {
            var mirrorLoc = (x + xx) + (y + (mirrorYCount - 1) - yy) * this.fieldPerLine;
            this.fields[mirrorLoc].truthmapID = this.fields[loc].truthmapID + mirrorXCount * mirrorYCount;
          } else {
            var mirrorLoc = (x + (mirrorXCount - 1) - xx) + (y + yy) * this.fieldPerLine;
            this.fields[mirrorLoc].truthmapID = this.fields[loc].truthmapID + mirrorYCount * mirrorYCount;
          }
        }
      }
      if (direction === 0) {
        mirrorYCount = mirrorYCount * 2;
        x = mirrorXCount;
        y = 0;
        direction = 1;
      } else {
        mirrorXCount = mirrorXCount * 2;
        y = mirrorYCount;
        x = 0;
        direction = 0;
      }
      loop++;
    }

  };

  this.getKVFieldsCount = function() {
    return this.fields.length;
  };

  this.getKVFieldPositionX = function(fieldId) {
    return this.fields[fieldId].position[0];
  };

  this.getKVFieldPositionY = function(fieldId) {
    return this.fields[fieldId].position[1];
  };

  this.getKVFieldTruthmapID = function(fieldId) {
    return this.fields[fieldId].truthmapID;
  };

  this.getKVFieldValue = function(fieldId) {
    return this.fields[fieldId].value;
  };

  this.activated = function(fieldId) {
    
    this.fields[fieldId].value += 1;
    if(this.allowDontCare) {
      if (this.fields[fieldId].value > 2) this.fields[fieldId].value = 0;
    }else{
      if (this.fields[fieldId].value> 1) this.fields[fieldId].value = 0;
    }

    this.qmc.data.setFuncData(this.fields[fieldId].truthmapID, this.fields[fieldId].value);
    this.qmc.data.compute();
    this.qmc.update();
    this.compute();
  };

  this.random = function() {
    for (var i in this.fields) {
	  if(this.allowDontCare) {
        this.fields[i].value = Math.floor(Math.random() * 3);
	  }else{
	    this.fields[i].value = Math.floor(Math.random() * 2);
	  }
      this.qmc.data.setFuncData(this.fields[i].truthmapID, this.fields[i].value);
    }
    this.qmc.data.compute();
    this.qmc.update();
    this.compute();
  };

  this.clear = function() {
    for (var i in this.fields) {
      this.fields[i].value = 0;
      this.qmc.data.setFuncData(this.fields[i].truthmapID, this.fields[i].value);
    }
    this.qmc.data.compute();
    this.qmc.update();
    this.compute();
  };

  this.compute = function() {
  
    this.blocks.length = 0;

    var localFieldsValues = new Array();

    for (var m = 0; m < this.qmc.data.minimalTermPrims.length; m++) {
      var minPrim = this.qmc.data.minimalTermPrims[m];

      localFieldsValues.length = 0;
      for (var i in this.fields) {
        if (this.fields[i].truthmapID in minPrim.implicant.imp) {
          localFieldsValues.push(1);
        } else {
          localFieldsValues.push(0);
        }
      }

      var maxX = Math.floor(Math.log(this.fieldPerLine) / Math.LN2);
      var maxY = Math.floor(Math.log(this.fieldLines) / Math.LN2);

      // this might be computationally expensive (computing all possible blocks)
      for (var x = maxX; x >= 0; x--) {
        for (var y = maxY; y >= 0; y--) {
          var px = Math.pow(2, x);
          var py = Math.pow(2, y);
          var stepI = Math.max(Math.floor(py / 2), 1);
          var stepJ = Math.max(Math.floor(px / 2), 1);
          for (var i = 0; i < this.fieldLines; i += stepI) {
            for (var j = 0; j < this.fieldPerLine; j += stepJ) {

              var id = i * this.fieldPerLine + j;

              if (localFieldsValues[id] === 1) {

                // search zero
                var noZero = true;
                for (var xx = 0; xx < px && noZero; xx++) {
                  for (var yy = 0; yy < py && noZero; yy++) {
                    var otherId = ((i + yy) % this.fieldLines) * this.fieldPerLine + ((j + xx) % this.fieldPerLine);
                    if (localFieldsValues[otherId] === 0)
                      noZero = false;
                  }
                }

                if (noZero) {
                  var block = new KVBlock();
                  block.fieldID = id;
                  block.dimx = px;
                  block.dimy = py;
                  block.color = minPrim.color;
                  this.blocks.push(block);
                  if (true) { //clearing all 1s
                    for (var xx = 0; xx < px; xx++) {
                      for (var yy = 0; yy < py; yy++) {
                        var otherId = ((i + yy) % this.fieldLines) * this.fieldPerLine + ((j + xx) % this.fieldPerLine);
                        localFieldsValues[otherId] = 0;
                      }
                    }
                  }

                } // end if(noZero)
              } // end if (localFieldsValues[id] === 1)
            } // end j
          } // end i
        } // end y
      } // end x
    } // end m
  };
}

function KarnaughMap(parentDivId, qmcRef) {
  var data = new KarnaughMapDataCtrl(qmcRef);
  var qmc = qmcRef;
  var canvas;
  var divId = parentDivId;
  var fieldColor = "rgba(133, 178, 255, 1.0)";
  var hooveredKVFieldColor = "rgba(170, 215, 255, 1.0)";
  var hooveredElement = -1;
  var hooveredKVField = -1;
  var uiElements = new Array();
  var that = this;
  var overlays = new Array();
  var overlayStyle = 'position:absolute; font-family:"Times New Roman",Georgia,Serif; visibility:inherit;';
  var overlayStyle2 = overlayStyle + 'border: 1px solid gray; background:white; pointer-events:none;';
  var resultStyle = 'position:inline; font-family:"Times New Roman",Georgia,Serif; visibility:inherit;';
  this.init = function() {
    
    data.init(4);
   
    canvas = document.createElement('canvas');
    if(!canvas) console.log("KarnaughMap error: can not create a canvas element");
    canvas.id = parentDivId + "_KarnaughMap";
    canvas.width = data.fieldBorder + data.fieldPerLine * data.fieldWidth + 20;
    canvas.height= data.fieldBorder  + data.fieldLines * data.fieldHeight + 20;
    document.body.appendChild(canvas);
    
    var parent = document.getElementById(divId);
    if(!parent) console.log("KarnaughMap error: can not find an element with the given name: " + divId);
    parent.appendChild(canvas);
 
    canvas.onmousedown = function(event) {
      canvasMouseDown(event);
    };
    canvas.onmousemove = function(event) {
      canvasMouseMove(event);
    };
    canvas.onmouseup = function(event) {
      canvasMouseUp(event);
    };
    canvas.onmouseup = function(event) {
      canvasMouseUp(event);
    };
    
    createOverlays();
    this.update();
  };

  this.setNoOfVars = function(no) {
    
    var c = parseInt(no);
    if (c < 1 && c > 10) return;
    
    hooveredKVField = -1;
    data.init(c);
    createOverlays();
    canvas.width = data.fieldBorder + data.fieldPerLine * data.fieldWidth + 50;
    canvas.height= data.fieldBorder  + data.fieldLines * data.fieldHeight + 50;
    this.update();
  };

  this.allowDontCares = function(type) {
    if(type > 0) {
      data.allowDontCare = true;
    }else{
      data.allowDontCare = false;
    }
    data.clear();
    this.update();
  };


  this.genRandom = function() {
    data.random();
    this.update();
  };

  this.clear = function() {
    data.clear();
    this.update();
  };

  function createOverlays() {
    
    var parent = document.getElementById(divId);
    if(!parent) console.log("KarnaughMap error: can not find an element with the given name: " + divId);
    parent.setAttribute('style', 'position:relative;');
    
    // remove old ones
    for(var i in overlays) {
      parent.removeChild(overlays[i]);
    }
    overlays.length = 0;
    
    for (var i = 0; i < data.noOfVars + 2; i++) {
      var overlay = document.createElement('div');
      overlay.setAttribute('style', 'position:absolute; top:0px; left:0px; visibility:hidden;');
      overlay.innerHTML = "overlay" + i;
      document.body.appendChild(overlay);

      parent.appendChild(overlay);
      overlays.push(overlay);
    }
  }



  function drawKVField(fieldId, ctx) {

    var fieldPosX = data.getKVFieldPositionX(fieldId);
    var fieldPosY = data.getKVFieldPositionY(fieldId);
    var truthmapID = data.getKVFieldTruthmapID(fieldId);
    var value = data.getKVFieldValue(fieldId);
    var dn = new UIElement(fieldPosX, fieldPosY, data.fieldWidth, data.fieldHeight, 0, fieldId, 0, 0);

    ctx.strokeStyle = "rgba(0, 0, 0, 1.0)";
    ctx.fillStyle = "rgba(255, 255, 255, 1.0)";
    if (fieldId === hooveredKVField) {
      ctx.fillStyle = hooveredKVFieldColor;
    }

    var dx = dn.x2 - dn.x;
    var dy = dn.y2 - dn.y;
    ctx.strokeRect(dn.x, dn.y, dx, dy);
    ctx.fillRect(dn.x, dn.y, dx, dy);
	ctx.fillStyle = "rgba(0, 0, 0, 1.0)";
	if(value >=2) {
      value = "X";
	  ctx.fillStyle = "rgba(200, 200, 200, 1.0)";
    }
    ctx.font = '20pt sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText(value, dn.x + Math.floor(dx/2), dn.y2 -  Math.floor(dx/4)); 

    uiElements.push(dn);
    if (true) {
      ctx.fillStyle = "rgba(0, 0, 0, 1.0)";
      ctx.textAlign = 'left';
      ctx.font = '8pt sans-serif';
      ctx.fillText(truthmapID, dn.x, dn.y2); 
    }
  }

  function drawRoundRect(ctx, x, y, width, height, radius) {
    var x1 = x + width;
    var y1 = y + height;
    
    ctx.beginPath();
    ctx.moveTo(x + radius, y);
    ctx.lineTo(x1 - radius, y);
    ctx.quadraticCurveTo(x1, y, x1, y + radius);
    ctx.lineTo(x1, y1 - radius);
    ctx.quadraticCurveTo(x1, y1, x1 - radius, y1);
    ctx.lineTo(x + radius, y1);
    ctx.quadraticCurveTo(x, y1, x, y1 - radius);
    ctx.lineTo(x, y + radius);
    ctx.quadraticCurveTo(x, y, x + radius, y);
    ctx.closePath();
    ctx.stroke();
  }

  function drawRoundRectOpenRightLeft(ctx, x, y, w, height, radius, offset) {
    
    var width = w / 2 + Math.floor(data.fieldWidth * 0.6);
    
    var x1 = x + width;
    var y1 = y + height;
  
    ctx.beginPath();
    ctx.moveTo(x1 - radius, y1);
    ctx.lineTo(x + radius, y1);
    ctx.quadraticCurveTo(x, y1, x, y1 - radius);
    ctx.lineTo(x, y + radius);
    ctx.quadraticCurveTo(x, y, x + radius, y);
    ctx.lineTo(x1 - radius, y);
    ctx.stroke();
    
    x1 = x + w + offset;
    x = x + offset + w/2 - Math.floor(data.fieldWidth * 0.6);
    ctx.beginPath();
    ctx.moveTo(x + radius, y);
    ctx.lineTo(x1 - radius, y);
    ctx.quadraticCurveTo(x1, y, x1, y + radius);
    ctx.lineTo(x1, y1 - radius);
    ctx.quadraticCurveTo(x1, y1, x1 - radius, y1);
    ctx.lineTo(x + radius, y1);
    ctx.stroke();
  }

  function drawRoundRectOpenTopDown(ctx, x, y, width, h, radius, offset) {
    
    //var width = w / 2 
    
    var height = h/2 + Math.floor(data.fieldHeight * 0.6);
    var x1 = x + width;
    var y1 = y + height;
  
    ctx.beginPath();
    ctx.moveTo(x1, y1 - radius);
    ctx.lineTo(x1, y + radius);
    ctx.quadraticCurveTo(x1, y, x1 - radius, y);
    ctx.lineTo(x + radius, y);
    ctx.quadraticCurveTo(x, y, x, y + radius);
    ctx.lineTo(x, y1 - radius);
    ctx.stroke();
   
    y1 = y + h + offset;
    y = y + offset + h/2 - Math.floor(data.fieldHeight * 0.6);
    
    ctx.beginPath();
    ctx.moveTo(x, y + radius);
    ctx.lineTo(x, y1 - radius);
    ctx.quadraticCurveTo(x, y1, x + radius, y1);
    ctx.lineTo(x1 - radius, y1);
    ctx.quadraticCurveTo(x1, y1, x1, y1 - radius);
    ctx.lineTo(x1, y + radius);
    ctx.stroke();
  }
  

  function drawRoundRectAllOpen(ctx, xx, yy, w, h, radius, offsetX, offsetY) {
    var height = h/2 + Math.floor(data.fieldHeight * 0.6);
    var width = w / 2 + Math.floor(data.fieldWidth * 0.6);
    
    var x = xx;
    var y = yy;
    var x1 = xx + width;
    var y1 = yy + height;
  
    ctx.beginPath();
    ctx.moveTo(x1 - radius, y);
    ctx.lineTo(x + radius, y);
    ctx.quadraticCurveTo(x, y, x, y + radius);
    ctx.lineTo(x, y1 - radius);
    ctx.stroke();
    
    x1 = xx + w + offsetX;
    x = xx + offsetX + w/2 - Math.floor(data.fieldWidth * 0.6);
    ctx.beginPath();
    ctx.moveTo(x + radius, y);
    ctx.lineTo(x1 - radius, y);
    ctx.quadraticCurveTo(x1, y, x1, y + radius);
    ctx.lineTo(x1, y1 - radius);
    ctx.stroke();
    
    y1 = yy + h + offsetY;
    y = yy + offsetY + h/2 - Math.floor(data.fieldHeight * 0.6);
    x = xx;
    x1 = xx + width;
    ctx.beginPath();
    ctx.moveTo(x, y + radius);
    ctx.lineTo(x, y1 - radius);
    ctx.quadraticCurveTo(x, y1, x + radius, y1);
    ctx.lineTo(x1 - radius, y1);
    ctx.stroke();
    
    x1 = xx + w + offsetX;
    x = xx + offsetX + w/2 - Math.floor(data.fieldWidth * 0.6);
    ctx.beginPath();
    ctx.moveTo(x1, y + radius);
    ctx.lineTo(x1, y1 - radius);
    ctx.quadraticCurveTo(x1, y1, x1 - radius, y1);
    ctx.lineTo(x + radius, y1);
    ctx.stroke();
    
  }

  function drawKVBlock(blockId, ctx) {
    var fieldId = data.blocks[blockId].fieldID;
   
    
    var x0 = data.getKVFieldPositionX(fieldId);
    var y0 = data.getKVFieldPositionY(fieldId);
    var dx = data.blocks[blockId].dimx * data.fieldWidth; 
    var dy = data.blocks[blockId].dimy * data.fieldHeight;        
    var colorStr = "rgba(" + data.blocks[blockId].color[0] + "," + data.blocks[blockId].color[1] + ","  + data.blocks[blockId].color[2] + ", 1.0)";
    ctx.strokeStyle = colorStr;
    
    var offsetX = (data.fieldWidth * data.fieldPerLine);
    var offsetY = (data.fieldHeight * data.fieldLines);
    var overX = (x0 + dx > offsetX + data.fieldBorder);
    var overY = (y0 + dy > offsetY + data.fieldBorder);
    if (overX && overY) {
      drawRoundRectAllOpen(ctx, x0 + 2, y0 + 2, dx - 4, dy - 4, 17, -offsetX, -offsetY);
    } else {
      if (overX) {
        drawRoundRectOpenRightLeft(ctx, x0 + 2, y0 + 2, dx - 4, dy - 4, 17, -offsetX);
      } else {
        if (overY) {
          drawRoundRectOpenTopDown(ctx, x0 + 2, y0 + 2, dx - 4, dy - 4, 17, -offsetY);
        } else {
          drawRoundRect(ctx, x0 + 2, y0 + 2, dx - 4, dy - 4, 17);
        }
      }
    }
  }

  function drawKVFields(ctx) {
    var count = data.getKVFieldsCount();
    for (var i = 0; i < count; i++) {
      drawKVField(i, ctx);
    }
  }
  
  function drawKVBlocks(ctx) {
    var count = data.blocks.length;
    for (var i = 0; i < count; i++) {
      drawKVBlock(i, ctx);
    }
  }
  

  this.update = function() {
   
    canvas.width = canvas.width;
    
    uiElements.length = 0;
    var ctx = canvas.getContext('2d');
    ctx.strokeStyle = '#000000';
    
    
    // draw grid
    if (false) {
      ctx.strokeStyle = '#808080';
      var stepsX = 20.0 - 0.0;
      var stepsY = 20.0 - 0.0;

      var lx = 0 % stepsX;
      var ly = 0 % stepsY;
      var Lx = 0 % (stepsX * 5.0);
      if (Lx < 0.0)
        Lx += (stepsX * 5.0);
      var Ly = 0 % (stepsY * 5.0);
      if (Ly < 0.0)
        Ly += (stepsY * 5.0);

      while (lx < canvas.width) {
        if (Math.abs(Lx - lx) < 0.001) {
          ctx.strokeStyle = '#404040';
          Lx += (stepsX * 5.0);
        } else {
          ctx.strokeStyle = '#808080';
        }
        ctx.beginPath();
        ctx.moveTo(lx, 0);
        ctx.lineTo(lx, canvas.height);
        ctx.stroke();
        lx += stepsX;
      }

      while (ly < canvas.height) {
        if (Math.abs(Ly - ly) < 0.001) {
          ctx.strokeStyle = '#404040';
          Ly += (stepsY * 5.0);
        } else {
          ctx.strokeStyle = '#808080';
        }
        ctx.beginPath();
        ctx.moveTo(0, ly);
        ctx.lineTo(canvas.width, ly);
        ctx.stroke();
        ly += stepsY;
      }
    }

    ctx.lineWidth = 1;
    
    // draws all fields
    drawKVFields(ctx);
    
    ctx.lineWidth = 3;
    // draws all blocks
    drawKVBlocks(ctx);
    
    // draw labels
    if(overlays.length !== data.noOfVars+2) console.log("KarnaughMap error: overlay not available");
    
    ctx.strokeStyle = "rgba(0, 0, 0, 1.0)";
    ctx.lineWidth = 2;
  
    var labelNum = 1;
    var labelPos = 10;
    var k = 0;
    while(k < data.noOfVars) {
      
      overlays[k].innerHTML = "<i>x</i><sub><small>" + k + "</small></sub>"
      
      for (var x = 0; x < data.fieldPerLine; x++) {
        var bits = data.getKVFieldTruthmapID(x);
        
        if ((bits & labelNum) === labelNum) {
          var x0 = data.fieldWidth * x + data.fieldBorder;
          var x1 = data.fieldWidth * (x + 1) + data.fieldBorder;
          ctx.beginPath();
          ctx.moveTo(x0, labelPos-2); // start marker
          ctx.lineTo(x0, labelPos+2);
          
          ctx.moveTo(x0, labelPos);
          ctx.lineTo(x1, labelPos);
          
          ctx.moveTo(x1, labelPos-2); // end marker
          ctx.lineTo(x1, labelPos+2);
          ctx.stroke();
          
          //ctx.fillText("1", x0+(x1-x0)/2 , labelPos-2);
          var style = overlayStyle + 'top:' +(labelPos-10) +'px; left:' +(x1+ 5)+'px;';
          overlays[k].setAttribute('style', style);
        }
      }
      k++;
      if (k < data.noOfVars) {
        
        overlays[k].innerHTML = "<i>x</i><sub><small>" + k + "</small></sub>";
        
        labelNum = labelNum << 1; // move bit to left

        for (var y = 0; y < data.fieldLines; y++) {
          var bits = data.getKVFieldTruthmapID(y * data.fieldPerLine);
          if ((bits & labelNum) === labelNum) {
            var x0 = data.fieldHeight * y + data.fieldBorder;
            var x1 = data.fieldHeight * (y + 1) + data.fieldBorder;
            ctx.beginPath();
            
            ctx.moveTo(labelPos-2, x0); // start marker
            ctx.lineTo(labelPos+2, x0);
            
            ctx.moveTo(labelPos, x0);
            ctx.lineTo(labelPos, x1);
            
            ctx.moveTo(labelPos-2, x1); // end marker
            ctx.lineTo(labelPos+2, x1);
               
            ctx.stroke();
            var style = overlayStyle + 'top:' +(x1)+'px; left:' +(labelPos-5) +'px;';
            overlays[k].setAttribute('style', style);
          }
        }
        labelNum = labelNum << 1; // move bit to left
        labelPos += 20;
        k++;
      }
    }
    ctx.lineWidth = 1;
     
    
    // draw binary value
    if(hooveredKVField >= 0 && hooveredKVField  < data.getKVFieldsCount()) {
      var truthmapID = data.getKVFieldTruthmapID(hooveredKVField);
      var binString = truthmapID.toString(2);
      while(binString.length < data.noOfVars) binString = "0" + binString;
      
      var valueString = "";
      for(var z=0; z < binString.length; z++) {
        valueString += binString[z];
        if(z < binString.length-1) valueString += ",";
      }
	  
	  var value = data.getKVFieldValue(hooveredKVField);
	  if(value >= 2) value = "X";
      valueString = "&nbsp;f(" + valueString + ") = "+ value;
      //valueString += " (ID: " + hooveredKVField + ")";
      var textX = Math.floor(hooveredKVField % data.fieldPerLine) * data.fieldWidth + Math.floor(data.fieldWidth*0.8) + data.fieldBorder;
      var textY = Math.floor(hooveredKVField / data.fieldPerLine) * data.fieldHeight + Math.floor(data.fieldHeight*0.1) + data.fieldBorder;
      var style = overlayStyle2 + 'top:' +textY+'px; left:' +textX+'px;';
      overlays[data.noOfVars].setAttribute('style', style);
      overlays[data.noOfVars].innerHTML = valueString;
    }else{ 
      overlays[data.noOfVars].innerHTML = "";
      var style = 'visibility:hidden;';
      overlays[data.noOfVars].setAttribute('style', style);
    }
    
    // draw minterm
    var termX = data.fieldBorder;
    var termY = data.fieldHeight * data.fieldLines + data.fieldBorder;
    var termStyle = resultStyle + 'max-width:' + data.fieldPerLine * data.fieldWidth + 'px;';
    overlays[data.noOfVars+1].setAttribute('style', termStyle);
    overlays[data.noOfVars+1].innerHTML = "<span class='qmcMathFont'><i>y</i>&nbsp;=&nbsp;" + qmc.data.coloredMinimalTerm +"</span></p>"
  };
  
  function mouseOverElement(pos) {
    var selectedElement = -1;
    for (var n in uiElements) {
      if (uiElements[n].type !== 2) {
        // not of type "connection"
        if (uiElements[n].x - 1 < pos.x && 
            uiElements[n].x2 + 1 > pos.x && 
            uiElements[n].y - 1 < pos.y && 
            uiElements[n].y2 + 1 > pos.y)
        {
          selectedElement = n;
        }
      } 
    }
    return selectedElement;
  }
  
  function canvasMouseDown(event) {
    var pos = getMouse(event);
    
    // handle selection
    if (!event.altKey && event.which === 1) {
      var selectedElement = mouseOverElement(pos);
      if (selectedElement !== -1) {
        // handle field selection
        if (uiElements[selectedElement].type === 0) {
          var newSelectedKVField = uiElements[selectedElement].ref;
          data.activated(newSelectedKVField);
        }
      }
      that.update();
    } 
    event.preventDefault();
  }

  function canvasMouseUp(event) {
  }

  function canvasMouseMove(event) {
    var pos = getMouse(event);

    hooveredKVField = -1;
    var oldHooveredElement = hooveredElement;
    hooveredElement = mouseOverElement(pos);

    if (hooveredElement !== -1) {
        hooveredKVField = uiElements[hooveredElement].ref;
    }
    if (oldHooveredElement !== hooveredElement) that.update();
    oldPos = pos;
    event.preventDefault();
  }

  function getMouse(e) {
    var element = canvas;
    var offsetX = 0, offsetY = 0, mx, my;

    // compute the total offset
    if (element.offsetParent !== undefined) {
      do {
        offsetX += element.offsetLeft;
        offsetY += element.offsetTop;
      } while ((element = element.offsetParent));
    }

    mx = e.pageX - offsetX;
    my = e.pageY - offsetY;

    return {x: mx, y: my};
  }
}