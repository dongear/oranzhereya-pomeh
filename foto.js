(function(){
"use strict";
/* Фото: снимок проходит через тот же грязный порог, что растения и вывески,
   а из тёмных мест фото растёт био-органика: рога, отростки, подтёки. Фото никуда не загружается. */

/* ---------- utils ---------- */
const $=id=>document.getElementById(id);
const TAU=Math.PI*2;
function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
const lerp=(a,b,t)=>a+(b-a)*t;
const angDiff=(a,b)=>((a-b)%TAU+3*Math.PI)%TAU-Math.PI;
function hashInts(a,b){let h=Math.imul((a|0)^0x9E3779B9,0x85EBCA6B)^(b|0);h=Math.imul(h^(h>>>13),0xC2B2AE35);return(h^(h>>>16))|0}
// зеркальный угол: m=1 как есть, m=-1 отражён слева направо
const mA=(a,m)=>m>0?a:Math.PI-a;
const note=$("note");
function setNote(t,err){note.textContent=t;note.classList.toggle("err",!!err)}

const PALETTES={
  paper:{name:"Белый",bg:"#FFFFFF",ink:"#111111"},
  night:{name:"Чёрный",bg:"#0B0B0B",ink:"#F0F0F0"}
};

/* ---------- шарики, грязь, блик (как в app.js) ---------- */
const K0="#000",WH="#fff";
let LW=1; // единица толщины линии в координатах фото
let BALL=null,BALLD=null;
function ballSprite(dark){
  const have=dark?BALLD:BALL;if(have)return have;
  const S=128,c=document.createElement("canvas");c.width=c.height=S;const g=c.getContext("2d");
  const gr=g.createRadialGradient(S*0.34,S*0.3,S*0.02,S*0.5,S*0.5,S*0.5);
  (dark?[[0,"#e2e2e2"],[0.45,"#a8a8a8"],[0.78,"#454545"],[0.94,"#111"],[1,"#000"]]:[[0,"#fff"],[0.45,"#f3f3f3"],[0.7,"#cdcdcd"],[0.86,"#707070"],[0.95,"#222"],[1,"#000"]])
    .forEach(s=>gr.addColorStop(s[0],s[1]));
  g.fillStyle=gr;g.beginPath();g.arc(S/2,S/2,S/2,0,TAU);g.fill();
  if(dark)BALLD=c;else BALL=c;return c;
}
const ball=(ctx,x,y,r,dark)=>{if(r>0.3)ctx.drawImage(ballSprite(dark),x-r,y-r,r*2,r*2)};
const GRIME=[];
function grime(ctx,x,y,r,v){
  if(!GRIME.length)for(let k=0;k<3;k++){const S=128,c=document.createElement("canvas");c.width=c.height=S;const g=c.getContext("2d"),rr=mulberry32(31+k);g.fillStyle="#000";
    for(let i=0;i<700;i++){const a=rr()*TAU,d=Math.pow(rr(),0.7)*S*0.48,px=S/2+Math.cos(a)*d,py=S/2+Math.sin(a)*d;g.globalAlpha=(1-d/(S*0.5))*0.9;g.beginPath();g.arc(px,py,0.6+rr()*rr()*4,0,TAU);g.fill()}
    for(let i=0;i<5;i++){g.globalAlpha=0.5;g.beginPath();g.ellipse(S/2+(rr()-.5)*S*0.5,S/2+(rr()-.5)*S*0.5,S*(0.04+rr()*0.1),S*(0.02+rr()*0.05),rr()*3,0,TAU);g.fill()}
    GRIME.push(c)}
  ctx.drawImage(GRIME[v%3],x-r,y-r,r*2,r*2);
}
let CORE=null;
function core(ctx,x,y,r){
  if(!CORE){const S=128;CORE=document.createElement("canvas");CORE.width=CORE.height=S;const g=CORE.getContext("2d"),gr=g.createRadialGradient(S/2,S/2,0,S/2,S/2,S/2);
    gr.addColorStop(0,"rgba(255,255,255,0.85)");gr.addColorStop(0.45,"rgba(235,235,235,0.7)");gr.addColorStop(0.75,"rgba(205,205,205,0.35)");gr.addColorStop(1,"rgba(200,200,200,0)");g.fillStyle=gr;g.fillRect(0,0,S,S)}
  if(r>0.3)ctx.drawImage(CORE,x-r*0.3-r*0.78,y-r*0.34-r*0.78,r*1.56,r*1.56);
}
function strokeLine(ctx,pts,col,w){
  ctx.beginPath();ctx.moveTo(pts[0][0],pts[0][1]);for(let i=1;i<pts.length;i++)ctx.lineTo(pts[i][0],pts[i][1]);
  ctx.globalAlpha=1;ctx.strokeStyle=col;ctx.lineWidth=w;ctx.lineCap="round";ctx.lineJoin="round";ctx.stroke();
}
function jitter(pts,amp,r){
  return pts.map((p,i)=>{if(!i)return p;const q=pts[i-1],a=Math.atan2(p[1]-q[1],p[0]-q[0])+Math.PI/2,d=(r()-.5)*2*amp;
    return [p[0]+Math.cos(a)*d,p[1]+Math.sin(a)*d]});
}
// яйцо-кокон; f=-1 отражает трещины для симметрии
function drawEgg(ctx,e){
  ctx.save();ctx.translate(e.x,e.y);ctx.rotate(e.a);ctx.scale(1,e.f);ctx.globalAlpha=1;
  ctx.drawImage(ballSprite(e.dark),0,-e.Wd,e.L,e.Wd*2);
  ctx.strokeStyle=K0;ctx.lineCap="round";ctx.lineWidth=LW*1.4;ctx.globalAlpha=0.7;ctx.beginPath();
  e.cracks.forEach(c=>{ctx.moveTo(c[0][0],c[0][1]);for(let i=1;i<c.length;i++)ctx.lineTo(c[i][0],c[i][1])});ctx.stroke();
  ctx.globalAlpha=1;ctx.fillStyle=K0;ctx.beginPath();ctx.ellipse(e.L*0.88,0,e.L*0.07,e.Wd*0.32,0,0,TAU);ctx.fill();
  ctx.restore();
}
// рот или глазница: валик из шариков, зубы внутрь, чёрная глубина
function drawOrifice(ctx,o){
  const R=o.r;ctx.globalAlpha=1;
  ball(ctx,o.x,o.y,R*1.1,true);
  for(let k=0;k<o.lips.length;k++){const a=o.rot+k/o.lips.length*TAU;ball(ctx,o.x+Math.cos(a)*R*0.74,o.y+Math.sin(a)*R*0.74,R*0.34*o.lips[k])}
  ctx.beginPath();ctx.ellipse(o.x,o.y,R*0.52,R*0.44,o.rot,0,TAU);ctx.fillStyle=K0;ctx.fill();
  if(o.teeth){ctx.beginPath();for(let k=0;k<o.teeth;k++){const a=o.rot+k/o.teeth*TAU+0.2,c=Math.cos(a),si=Math.sin(a),r0=R*0.5,r1=R*(0.22+0.12*(k%2));
    ctx.moveTo(o.x+c*r0-si*R*0.06,o.y+si*r0+c*R*0.06);ctx.lineTo(o.x+c*r1,o.y+si*r1);ctx.lineTo(o.x+c*r0+si*R*0.06,o.y+si*r0-c*R*0.06)}
    ctx.fillStyle="#d8d8d8";ctx.fill()}
}


/* ---------- фото: яркость и маска тёмных мест ---------- */
const CAP=2000; // длинная сторона результата
const mk0=()=>document.createElement("canvas");
// исходник приводится к CAP по длинной стороне, яркость считается один раз
function prepPhoto(img){
  const iw=img.naturalWidth||img.width,ih=img.naturalHeight||img.height,k=CAP/Math.max(iw,ih),W=Math.round(iw*k),H=Math.round(ih*k);
  const c=mk0();c.width=W;c.height=H;const g=c.getContext("2d",{willReadFrequently:true});
  g.fillStyle="#fff";g.fillRect(0,0,W,H);g.imageSmoothingQuality="high";g.drawImage(img,0,0,W,H);
  const d=g.getImageData(0,0,W,H).data,lum=new Uint8Array(W*H);
  for(let i=0,q=0;q<lum.length;q++,i+=4)lum[q]=Math.round(d[i]*0.299+d[i+1]*0.587+d[i+2]*0.114);
  return {W,H,src:c,lum};
}
// «Тень»: кривая яркости. Порог рассчитан на светлые рендеры, поэтому средние тона фото поднимаются,
// иначе всё зальёт чёрным. 0 — светло, почти одни контуры; 1 — темно
const toneMap=(l,t)=>255*Math.pow(l/255,0.18+t*0.7);
function grayPhoto(P,t){
  const c=mk0();c.width=P.W;c.height=P.H;const g=c.getContext("2d"),img=g.createImageData(P.W,P.H),d=img.data;
  for(let q=0,i=0;q<P.lum.length;q++,i+=4){const v=toneMap(P.lum[q],t);d[i]=d[i+1]=d[i+2]=v;d[i+3]=255}
  g.putImageData(img,0,0);return c;
}
// маска тёмных мест на грубой сетке (размытие уменьшением) и расстояние до края, как у букв
function photoMask(P,t){
  const S=Math.max(P.W,P.H)/320,gw=Math.ceil(P.W/S),gh=Math.ceil(P.H/S);
  const c=mk0();c.width=gw;c.height=gh;const g=c.getContext("2d",{willReadFrequently:true});g.imageSmoothingQuality="high";g.drawImage(P.src,0,0,gw,gh);
  const a=g.getImageData(0,0,gw,gh).data,d=new Float32Array(gw*gh);
  for(let q=0,i=0;q<d.length;q++,i+=4)d[q]=a[i]*0.299+a[i+1]*0.587+a[i+2]*0.114<60+t*110?1e9:0; // тёмные места исходника
  const at=(x,y)=>x<0||y<0||x>=gw||y>=gh?0:d[y*gw+x],D=Math.SQRT2;
  for(let y=0;y<gh;y++)for(let x=0;x<gw;x++){const k=y*gw+x;if(d[k])d[k]=Math.min(d[k],at(x-1,y)+1,at(x,y-1)+1,at(x-1,y-1)+D,at(x+1,y-1)+D)}
  for(let y=gh-1;y>=0;y--)for(let x=gw-1;x>=0;x--){const k=y*gw+x;if(d[k])d[k]=Math.min(d[k],at(x+1,y)+1,at(x,y+1)+1,at(x+1,y+1)+D,at(x-1,y+1)+D)}
  return {gw,gh,d,at,S};
}

/* ---------- рост ---------- */
// K: ручки 0..1 — grow, spikes, drips, parts, rag. При «Росте» на нуле остаётся чистый фильтр
function build(P,gray,tone,seed,K){
  const items=[],lines=[];
  const ext=()=>{}; // кадр — само фото, рисунок за краем просто обрезается
  const add=(L,f)=>items.push({L,f});
  const R0=mulberry32(seed),T=Math.max(P.W,P.H)*0.016;
  add(-1,ctx=>{ctx.globalAlpha=1;ctx.drawImage(gray,0,0,P.W,P.H)});

  // край тёмных мест: точки роста с нормалью наружу
  const {gw,gh,d,at,S}=photoMask(P,tone),edges=[];
  for(let y=1;y<gh-1;y++)for(let x=1;x<gw-1;x++){if(!d[y*gw+x])continue;
    if(at(x-1,y)&&at(x+1,y)&&at(x,y-1)&&at(x,y+1))continue;
    let nx=at(x-1,y)-at(x+1,y),ny=at(x,y-1)-at(x,y+1);const l=Math.hypot(nx,ny);if(!l)continue;nx/=l;ny/=l;
    edges.push({x:(x+0.5)*S,y:(y+0.5)*S,nx,ny})}

  // ось конечности: плавное блуждание; m=-1 зеркалит все повороты
  function walk(r,x,y,a,len,w0,w1,o,m){
    const n=Math.max(6,Math.round(len/(T*0.12))),sl=len/n,ph=[r()*TAU,r()*TAU,r()*TAU],f1=0.15+r()*0.25,f2=0.5+r()*0.6,wild=o.wild==null?0.6:o.wild;
    const loopAt=o.loop?0.25+r()*0.4:-1,loopDir=r()<.5?-1:1;
    const pts=[[x,y]],angs=[a],ws=[w0];
    for(let i=1;i<=n;i++){const q=i/n;
      a+=m*((Math.sin(i*f1+ph[0])*0.05+Math.sin(i*f2+ph[1])*0.03)*wild*2+(r()-.5)*0.07*wild);
      if(o.grav)a+=angDiff(o.grav>0?Math.PI/2:-Math.PI/2,a)*Math.abs(o.grav);
      if(o.bend)a+=m*o.bend*Math.pow(q,3)*0.3;
      if(loopAt>=0&&q>loopAt&&q<loopAt+0.3)a+=m*loopDir*TAU/(0.3*n)*0.95;
      x+=Math.cos(a)*sl;y+=Math.sin(a)*sl;
      let w=lerp(w0,w1,Math.pow(q,0.85))*(1+0.18*Math.sin(i*0.3+ph[2])*(o.lumpy==null?1:o.lumpy));
      if(o.beads)w*=0.7+0.5*Math.abs(Math.sin(i*o.beads));
      pts.push([x,y]);angs.push(a);ws.push(Math.max(T*0.015,w));
    }
    return {pts,angs,ws};
  }
  // объём вдоль оси: шарики, блик, грязь, поры
  function limb(P,L,o,r){
    const ribbed=o.ribbed!=null?o.ribbed:r()<0.15,balls=[];let acc=0,sp=0.13;
    for(let i=0;i<P.pts.length;i++){if(i)acc+=Math.hypot(P.pts[i][0]-P.pts[i-1][0],P.pts[i][1]-P.pts[i-1][1]);
      if(i===0||acc>=sp*P.ws[i]){acc=0;sp=ribbed?0.18+r()*0.32:0.1+r()*0.08;balls.push([P.pts[i][0],P.pts[i][1],P.ws[i],ribbed&&r()<0.2||!!o.dark]);ext(P.pts[i][0],P.pts[i][1],P.ws[i])}}
    const gr=[];balls.forEach(b=>{if(r()<0.25+K.rag*0.4)gr.push([b[0]+b[2]*0.35,b[1]+b[2]*0.4,b[2]*(0.7+r()*0.7),Math.floor(r()*3),0.35+r()*0.5])});
    add(L,ctx=>{ctx.globalAlpha=1;balls.forEach(b=>ball(ctx,b[0],b[1],b[2],b[3]));if(!ribbed)balls.forEach(b=>core(ctx,b[0],b[1],b[2]));
      gr.forEach(g=>{ctx.globalAlpha=g[4];grime(ctx,g[0],g[1],g[2],g[3])});ctx.globalAlpha=1});
  }
  function mass(r,x,y,R,n,L,m){
    const balls=[];
    for(let k=0;k<n;k++){const a=r()*TAU,dd=Math.sqrt(r())*R*0.75,s=R*(0.25+r()*0.45),px=x+m*Math.cos(a)*dd,py=y+Math.sin(a)*dd;balls.push([px,py,s,r()<0.25]);ext(px,py,s)}
    balls.sort((p,q)=>p[1]-q[1]);
    add(L,ctx=>{ctx.globalAlpha=1;balls.forEach(b=>ball(ctx,b[0],b[1],b[2],b[3]))});
  }
  // часть тела на конце отростка
  function part(r,kind,x,y,a,R,m){
    if(kind==="claws"){
      mass(r,x,y,R*0.55,5,4,m);
      const n=3+Math.floor(r()*3);
      for(let k=0;k<n;k++){const off=(k/(n-1)-0.5)*2+(r()-.5)*0.4,ca=a+m*off;
        const P=walk(r,x+Math.cos(ca)*R*0.3,y+Math.sin(ca)*R*0.3,ca,R*(1.3+r()*1.1),R*0.2,R*0.02,{wild:0.4,bend:(off<0?1:-1)*(1.2+r()*1.5),lumpy:0.5,beads:r()<0.2?0.9:0},m);
        limb(P,4,{ribbed:r()<0.25},r)}
    }else if(kind==="eggs"){
      const n=1+Math.floor(r()*3);mass(r,x,y,R*0.5,4,4,m);
      for(let k=0;k<n;k++){const ea=a+m*((n>1?(k/(n-1)-0.5)*1.8:0)+(r()-.5)*0.4),L=R*(1.2+r()*0.8),Wd=L*(0.32+r()*0.12),cracks=[];
        for(let c=0;c<2+Math.floor(r()*3);c++){let px=L*(0.2+r()*0.5),py=(r()-.5)*Wd;const pts=[[px,py]];for(let j=0;j<5;j++){px+=L*0.08;py+=(r()-.5)*Wd*0.35;pts.push([px,clamp(py,-Wd*0.85,Wd*0.85)])}cracks.push(pts)}
        const e={x:x+Math.cos(ea)*R*0.2,y:y+Math.sin(ea)*R*0.2,a:ea,L,Wd,cracks,dark:r()<0.3,f:m};
        ext(e.x+Math.cos(ea)*L,e.y+Math.sin(ea)*L,Wd);ext(e.x,e.y,Wd);add(4,ctx=>drawEgg(ctx,e))}
    }else if(kind==="orifice"){
      const n=9+Math.floor(r()*6),lips=[];for(let k=0;k<n;k++)lips.push(0.7+r()*0.6);
      const o={x,y,r:R,lips,rot:mA(r()*TAU,m),teeth:r()<0.7?Math.round(6+r()*8):0};ext(x,y,R*1.4);add(4,ctx=>drawOrifice(ctx,o));
    }else if(kind==="spine"){
      const P=walk(r,x,y,a,R*3,R*0.4,R*0.1,{wild:0.5,beads:0.75,bend:(r()<.5?-1:1)*(2+r()*2),lumpy:0.2},m);
      limb(P,4,{ribbed:true},r);const e=P.pts[P.pts.length-1];mass(r,e[0],e[1],R*0.35,4,4,m);
    }else mass(r,x,y,R*1.2,8+Math.floor(r()*7),4,m);
  }
  const KINDS=["claws","eggs","orifice","spine","mass"];
  const pickKind=r=>KINDS[Math.floor(r()*KINDS.length)];

  // мелкие шипы вдоль отростка
  function thorns(P,r,m){
    for(let i=4;i<P.pts.length-2;i+=5+Math.floor(r()*6)){if(r()>K.spikes)continue;
      const s=r()<.5?-1:1,ca=P.angs[i]+m*s*(1+r()*0.4);
      const Q=walk(r,P.pts[i][0],P.pts[i][1],ca,P.ws[i]*(1.5+r()*2.5),P.ws[i]*0.4,T*0.015,{wild:0.2,bend:-s*1.5},m);limb(Q,2,{ribbed:false},r)}
  }

  // одно украшение из точки края; seed общий для пары, поэтому зеркальная копия совпадает по форме
  function deco(type,s,e,m){
    const r=mulberry32(s),x=e.x,y=e.y,nx=e.nx,ny=e.ny;let a=Math.atan2(ny,nx);
    if(type==="spike"){ // рог: к вертикали, если растёт сверху или снизу
      if(ny<-0.4)a+=angDiff(-Math.PI/2,a)*0.55;else if(ny>0.4)a+=angDiff(Math.PI/2,a)*0.55;
      const P=walk(r,x-nx*T*0.25,y-ny*T*0.25,a,T*(1+r()*4.5)*(0.25+K.spikes*1.3),T*(0.3+r()*0.2),T*0.02,{wild:0.25,bend:(r()-.5)*3,lumpy:0.4,beads:r()<0.2?1:0},m);
      limb(P,2,{ribbed:r()<0.3},r);
    }else if(type==="limb"){ // отросток с шипами и частью тела на конце
      const P=walk(r,x-nx*T*0.2,y-ny*T*0.2,a,T*(3+r()*7)*(0.3+K.grow*1.2),T*(0.28+r()*0.15),T*(0.04+r()*0.05),{wild:0.9,bend:(r()<.5?-1:1)*(1+r()*2.5),loop:r()<0.35,grav:ny>0.4?0.02:-0.01},m);
      limb(P,2,{},r);thorns(P,mulberry32(s^0x9E37),m);
      const rp=mulberry32(s^0x51ED),n=P.pts.length-1;
      if(rp()<K.parts)part(rp,pickKind(rp),P.pts[n][0],P.pts[n][1],P.angs[n],T*(0.6+rp()*0.5),m);
    }else{ // подтёк: жидкий или плотский
      if(r()<0.55){const len=T*(1+r()*5)*(0.5+K.drips),x0=x+(r()-.5)*T*0.3,pts=[[x0,y]];
        for(let i=1;i<=6;i++)pts.push([x0,y+len*i/6]);
        const l={pts:jitter(pts,T*0.03,r),w:T*(0.05+r()*0.06)};lines.push(l);l.pts.forEach(p=>ext(p[0],p[1],T*0.15))}
      else{const P=walk(r,x,y-T*0.1,Math.PI/2,T*(1.5+r()*4)*(0.5+K.drips),T*(0.2+r()*0.1),T*(0.1+r()*0.06),{wild:0.12,grav:0.12,beads:r()<0.5?0.6+r()*0.6:0,lumpy:0.3},m);
        limb(P,2,{ribbed:false},r);const e=P.pts[P.pts.length-1];mass(r,e[0],e[1],T*0.3,3,2,m)}
    }
  }

  const g=K.grow*1.5;
  if(g>0){
    const sh=edges.slice();for(let i=sh.length-1;i>0;i--){const j=Math.floor(R0()*(i+1));const t=sh[i];sh[i]=sh[j];sh[j]=t}
    const taken=[],near=(x,y,dd)=>taken.some(p=>Math.abs(p[0]-x)<dd&&Math.abs(p[1]-y)<dd);
    let idx=0;
    for(const e of sh){
      if(near(e.x,e.y,T*0.9))continue;taken.push([e.x,e.y]);
      const i=idx++,roll=mulberry32(hashInts(seed,i*7919+3))(),s=hashInts(seed,i*7919+5);
      const vert=Math.abs(e.ny)>0.55,ps=K.spikes*(vert?0.42:0.12)*g,pl=0.14*g,pd=e.ny>0.55?K.drips*0.5*g:0;
      const type=roll<ps?"spike":roll<ps+pl?"limb":roll<ps+pl+pd?"drip":null;
      if(type)deco(type,s,e,1);
    }
  }
  add(1,ctx=>{lines.forEach(l=>{strokeLine(ctx,l.pts,K0,Math.max(l.w,LW*1.6));const e=l.pts[l.pts.length-1];ball(ctx,e[0],e[1],Math.max(l.w*1.6,LW*2),true)})});

  items.sort((a,b)=>a.L-b.L);
  return {items,bb:{x0:0,y0:0},s:1,W:P.W,H:P.H,T,seed};
}

/* ---------- грязный порог (как в app.js) ---------- */
let NZ=null;
function noiseTile(){
  if(NZ)return NZ;
  const Sz=512,C=32,a=new Uint8Array(Sz*Sz),r=mulberry32(5),c=new Float32Array(C*C);
  for(let i=0;i<c.length;i++)c[i]=r();
  for(let y=0;y<Sz;y++)for(let x=0;x<Sz;x++){const fx=x/Sz*C,fy=y/Sz*C,x0=Math.floor(fx),y0=Math.floor(fy),tx=fx-x0,ty=fy-y0,
    g=(i,j)=>c[(j%C)*C+(i%C)],v=lerp(lerp(g(x0,y0),g(x0+1,y0),tx),lerp(g(x0,y0+1),g(x0+1,y0+1),tx),ty);
    a[y*Sz+x]=Math.round(clamp(v*0.55+r()*0.45,0,1)*255)}
  return NZ=a;
}
const hexRGB=h=>{const m=/^#?([0-9a-f]{6})$/i.exec(h);const v=m?parseInt(m[1],16):0;return [v>>16&255,v>>8&255,v&255]};
// болотная палитра: только тёмные, грязные цвета
const SWAMP=["#5A1A22","#3F1418","#23361F","#2F4A23","#3E4A1E","#4D4F22","#1C2A44","#18303A","#1E3B36",
  "#4A2E1A","#3A2A20","#5E3A1C","#3B1E33","#6A3418","#2B302A","#34402E"].map(hexRGB);
// цветные пятна: случайные точки, у каждой цвет из 3–5 болотных, пиксель берёт цвет ближайшей;
// координаты трясёт шум, поэтому границы пятен зернистые, как у ризографии. На чёрном фоне цвета светлее
function colorField(w,h,seed,dark){
  const r=mulberry32(seed),n=5+Math.floor(r()*8),pool=SWAMP.slice(),pal=[],pts=[],cols=[];
  for(let k=0,m=3+Math.floor(r()*3);k<m;k++)pal.push(pool.splice(Math.floor(r()*pool.length),1)[0]);
  for(let k=0;k<n;k++){pts.push([r()*w,r()*h]);const c=pal[Math.floor(r()*pal.length)];cols.push(dark?c.map(v=>Math.round(v+(255-v)*0.38)):c)}
  const N=noiseTile(),amp=Math.max(w,h)*0.07;
  return {cols,at(x,y){const jx=x+(N[((y>>1)&511)<<9|((x>>1)+57&511)]-128)/128*amp,jy=y+(N[((x>>1)+301&511)<<9|((y>>1)&511)]-128)/128*amp;
    let b=0,bd=Infinity;for(let k=0;k<pts.length;k++){const dx=pts[k][0]-jx,dy=pts[k][1]-jy,dd=dx*dx+dy*dy;if(dd<bd){bd=dd;b=k}}return b}};
}
const mk=()=>document.createElement("canvas");
const OFF=mk(),SMALL=mk(),MID=mk(),BLR=mk();
const pixSize=()=>1+Math.round(state.pix*7);
const cv=$("cv"),frame=$("frame");
let last=null; // последний 1-битный результат для SVG

function paint(M){
  const px=pixSize(),sc=1/px,w=Math.max(8,Math.round(M.W*sc)),h=Math.max(8,Math.round(M.H*sc));
  if(OFF.width!==w||OFF.height!==h){OFF.width=w;OFF.height=h;BLR.width=w;BLR.height=h}
  const o=OFF.getContext("2d",{willReadFrequently:true});
  o.setTransform(1,0,0,1,0,0);o.globalAlpha=1;o.fillStyle=WH;o.fillRect(0,0,w,h);
  LW=Math.max(1,px*0.7)/M.s;
  const k=M.s*sc;o.setTransform(k,0,0,k,-M.bb.x0*k,-M.bb.y0*k);
  M.items.forEach(it=>it.f(o));
  o.setTransform(1,0,0,1,0,0);o.globalAlpha=1;
  MID.width=Math.max(4,Math.round(w/4));MID.height=Math.max(4,Math.round(h/4));SMALL.width=Math.max(2,Math.round(w/14));SMALL.height=Math.max(2,Math.round(h/14));
  const mc=MID.getContext("2d"),smc=SMALL.getContext("2d"),bc=BLR.getContext("2d",{willReadFrequently:true});
  mc.imageSmoothingQuality=smc.imageSmoothingQuality=bc.imageSmoothingQuality="high";
  mc.drawImage(OFF,0,0,MID.width,MID.height);smc.drawImage(MID,0,0,SMALL.width,SMALL.height);
  bc.clearRect(0,0,w,h);bc.drawImage(SMALL,0,0,w,h);
  const img=o.getImageData(0,0,w,h),d=img.data,mean=bc.getImageData(0,0,w,h).data,N=noiseTile();
  const gray=new Uint8Array(w*h);for(let q=0,i=0;q<gray.length;q++,i+=4)gray[q]=d[i];
  const P=PALETTES[state.palette],ink=hexRGB(P.ink),bg=hexRGB(P.bg),tr=state.transparent,bits=new Uint8Array(w*h);
  const cf=state.colorMode==="color"?colorField(w,h,hashInts(M.seed,state.colorSeed*977+1),state.palette==="night"):null;
  const g=state.rag,deep=48+g*35,edge=4+(1-g)*6,nAmp=16+g*30,shake=0.4+g*1.4;
  for(let y=0,i=0,q=0;y<h;y++){const row=(y&511)<<9,row2=((y+211)&511)<<9;
    for(let x=0;x<w;x++,i+=4,q++){
      const sx=clamp(x+Math.round((N[row|((x+97)&511)]-128)/128*shake),0,w-1),sy=clamp(y+Math.round((N[row2|((x+31)&511)]-128)/128*shake),0,h-1);
      const v=gray[sy*w+sx],nz=(N[row|(x&511)]-128)/128,m=mean[i];
      const on=v<254&&(v<deep+nz*40||v-m<-edge+nz*nAmp*0.5||(v<242&&nz<-0.62+(242-v)/105));
      const ci=on&&cf?cf.at(x,y):0,fg=cf?cf.cols[ci]:ink;
      bits[q]=on?ci+1:0; // 0 — пусто, иначе номер цвета + 1
      if(tr){d[i]=fg[0];d[i+1]=fg[1];d[i+2]=fg[2];d[i+3]=on?255:0}
      else{const c=on?fg:bg;d[i]=c[0];d[i+1]=c[1];d[i+2]=c[2];d[i+3]=255}}}
  o.putImageData(img,0,0);
  if(cv.width!==M.W||cv.height!==M.H){cv.width=M.W;cv.height=M.H}
  const ctx=cv.getContext("2d");
  ctx.setTransform(1,0,0,1,0,0);ctx.clearRect(0,0,M.W,M.H);
  ctx.imageSmoothingEnabled=false;ctx.drawImage(OFF,0,0,M.W,M.H);ctx.imageSmoothingEnabled=true;
  last={w,h,bits,px,inks:cf?cf.cols.map(c=>"rgb("+c.join(",")+")"):[P.ink],bg:P.bg,tr};
}

// SVG из пикселей: каждая строка — полосы закрашенных клеток; в Figma это один векторный слой
// в цветном режиме каждый цвет — свой слой
function toSVG(L){
  const parts=L.inks.map(()=>[]);
  for(let y=0;y<L.h;y++){let x=0;const row=y*L.w;
    while(x<L.w){const v=L.bits[row+x];if(!v){x++;continue}const s=x;while(x<L.w&&L.bits[row+x]===v)x++;parts[v-1].push("M"+s+" "+y+"h"+(x-s)+"v1h-"+(x-s)+"z")}}
  const one=L.inks.length===1;
  return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 '+L.w+" "+L.h+'" width="'+L.w*L.px+'" height="'+L.h*L.px+'" shape-rendering="crispEdges">'+
    (L.tr?"":'<rect id="фон" width="'+L.w+'" height="'+L.h+'" fill="'+L.bg+'"/>')+
    parts.map((p,k)=>p.length?'<path id="'+(one?"фото":"цвет-"+(k+1))+'" fill="'+L.inks[k]+'" d="'+p.join("")+'"/>':"").join("")+'</svg>';
}

/* ---------- состояние ---------- */
const state={variant:0,palette:"paper",colorMode:"mono",colorSeed:0,transparent:false,
  tone:0.3,grow:0.35,spikes:0.55,drips:0.4,parts:0.4,rag:0.5,pix:0.29};
let model=null,photo=null,gray=null,grayTone=-1,photoName="",photoSeed=0;

function render(){
  if(!photo)return;
  if(grayTone!==state.tone){gray=grayPhoto(photo,state.tone);grayTone=state.tone}
  const K={grow:state.grow,spikes:state.spikes,drips:state.drips,parts:state.parts,rag:state.rag};
  model=build(photo,gray,state.tone,hashInts(photoSeed,state.variant*7919+1),K);
  frame.classList.remove("empty");frame.classList.toggle("checker",state.transparent);
  paint(model);
}
let pending=false;
const renderSoon=()=>{if(pending)return;pending=true;requestAnimationFrame(()=>{pending=false;render()});setTimeout(()=>{if(pending){pending=false;render()}},150)};

/* ---------- загрузка фото ---------- */
function loadFile(f){
  if(!f)return;
  if(f.type&&!f.type.startsWith("image/")){setNote("Нужна картинка: jpg, png или webp.",true);return}
  const url=URL.createObjectURL(f),img=new Image();
  img.onload=()=>{URL.revokeObjectURL(url);photo=prepPhoto(img);grayTone=-1;state.variant=0;
    photoName=(f.name||"фото").replace(/\.[^.]+$/,"");photoSeed=hashInts(photo.W*7919+photo.H,photo.lum[photo.lum.length>>1]*131+photo.lum[photo.lum.length>>2]);
    render();setNote("")};
  img.onerror=()=>{URL.revokeObjectURL(url);setNote("Не удалось открыть картинку.",true)};
  img.src=url;
}
$("file").addEventListener("change",e=>{loadFile(e.target.files[0]);e.target.value=""});
const drop=$("drop");
["dragenter","dragover"].forEach(t=>drop.addEventListener(t,e=>{e.preventDefault();drop.classList.add("over")}));
["dragleave","drop"].forEach(t=>drop.addEventListener(t,e=>{e.preventDefault();drop.classList.remove("over")}));
drop.addEventListener("drop",e=>{const f=e.dataTransfer&&e.dataTransfer.files[0];if(f)loadFile(f)});

/* ---------- сохранение ---------- */
let downloadsP=Promise.resolve(null);
try{if(window.claude&&typeof window.claude.use==="function")downloadsP=window.claude.use("downloads").catch(()=>null)}catch(e){}
async function saveBlob(blob,fname,okMsg){
  let dl=null;try{dl=await downloadsP}catch(e){}
  if(dl){
    try{await dl.save({filename:fname,data:blob});setNote(okMsg);return}
    catch(err){if(err&&err.code==="declined"){setNote("Сохранение отменено.");return}
      if(err&&err.code==="rate_limited"){setNote("Окно сохранения уже открыто.");return}}
  }
  try{const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=fname;document.body.append(a);a.click();a.remove();setNote(okMsg);return}catch(e){}
  setNote("Файл не скачался.",true);
}
const fileName=ext=>"фото_"+(photoName.replace(/[^\p{L}\p{N}]+/gu,"_").slice(0,24)||"без_имени")+"."+ext;
$("savePng").addEventListener("click",async()=>{if(!model)return;const blob=await new Promise(r=>cv.toBlob(r,"image/png"));saveBlob(blob,fileName("png"),"PNG сохранён.")});
$("saveSvg").addEventListener("click",()=>{if(!last)return;saveBlob(new Blob([toSVG(last)],{type:"image/svg+xml"}),fileName("svg"),"SVG сохранён.")});

/* ---------- управление ---------- */
function bindSeg(el,key){el.addEventListener("click",e=>{const b=e.target.closest("button");if(!b)return;
  state[key]=b.dataset.v;el.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",x===b));renderSoon()})}
const palWrap=$("palettes");
Object.entries(PALETTES).forEach(([k,p])=>{const b=document.createElement("button");b.dataset.v=k;b.setAttribute("aria-pressed",k===state.palette);b.textContent=p.name;palWrap.append(b)});
bindSeg(palWrap,"palette");bindSeg($("colorMode"),"colorMode");
$("colorMode").addEventListener("click",()=>{$("reshuffle").hidden=state.colorMode!=="color"});
$("reshuffle").addEventListener("click",()=>{state.colorSeed++;render()});
$("transparent").addEventListener("change",e=>{state.transparent=e.target.checked;renderSoon()});
$("again").addEventListener("click",()=>{state.variant++;render()});

/* ---------- ручки (как в app.js) ---------- */
const SVGNS="http://www.w3.org/2000/svg",A0=-135,A1=135;
function arcD(a0,a1){const r=19,p=a=>{const t=(a-90)*Math.PI/180;return (24+Math.cos(t)*r).toFixed(2)+" "+(24+Math.sin(t)*r).toFixed(2)};
  return "M "+p(a0)+" A "+r+" "+r+" 0 "+(a1-a0>180?1:0)+" 1 "+p(a1)}
function makeKnob(box,o){
  const el=document.createElement("div");el.className="knob";
  const dial=document.createElement("div");dial.className="knob-dial";dial.tabIndex=0;dial.setAttribute("role","slider");dial.setAttribute("aria-label",o.label);
  dial.setAttribute("aria-valuemin","0");dial.setAttribute("aria-valuemax","100");
  const svg=document.createElementNS(SVGNS,"svg");svg.setAttribute("viewBox","0 0 48 48");
  const mkS=(tag,cls)=>{const e=document.createElementNS(SVGNS,tag);e.setAttribute("class",cls);svg.append(e);return e};
  const track=mkS("path","k-track"),val=mkS("path","k-val"),cap=mkS("circle","k-cap"),ptr=mkS("line","k-ptr");
  track.setAttribute("d",arcD(A0,A1));cap.setAttribute("cx",24);cap.setAttribute("cy",24);cap.setAttribute("r",12);
  ptr.setAttribute("x1",24);ptr.setAttribute("y1",21);ptr.setAttribute("x2",24);ptr.setAttribute("y2",13);
  dial.append(svg);
  const lab=document.createElement("span");lab.className="knob-label";lab.textContent=o.label;
  const out=document.createElement("span");out.className="knob-value";
  el.append(dial,lab,out);box.append(el);
  let t=0,def=0;
  function draw(){const a=lerp(A0,A1,t);
    val.setAttribute("d",t>0.004?arcD(A0,a):"");ptr.setAttribute("transform","rotate("+a.toFixed(1)+" 24 24)");
    const txt=o.fmt(t);out.textContent=txt;dial.setAttribute("aria-valuenow",Math.round(t*100));dial.setAttribute("aria-valuetext",txt)}
  function setT(nt){nt=clamp(nt,0,1);if(nt===t)return;t=nt;draw();o.onInput(t)}
  let drag=null;
  dial.addEventListener("pointerdown",e=>{drag={y:e.clientY,t};dial.setPointerCapture(e.pointerId);dial.focus();e.preventDefault()});
  dial.addEventListener("pointermove",e=>{if(drag)setT(drag.t+(drag.y-e.clientY)/(e.shiftKey?600:160))});
  const end=()=>{drag=null};dial.addEventListener("pointerup",end);dial.addEventListener("pointercancel",end);
  dial.addEventListener("dblclick",()=>setT(def));
  dial.addEventListener("wheel",e=>{e.preventDefault();setT(t-Math.sign(e.deltaY)*0.03)},{passive:false});
  dial.addEventListener("keydown",e=>{const st=e.shiftKey?0.1:0.02,m={ArrowUp:st,ArrowRight:st,ArrowDown:-st,ArrowLeft:-st,PageUp:0.1,PageDown:-0.1}[e.key];
    if(m!=null){e.preventDefault();setT(t+m)}else if(e.key==="Home"){e.preventDefault();setT(0)}else if(e.key==="End"){e.preventDefault();setT(1)}});
  t=def=clamp(o.value,0,1);draw();
}
const pct=v=>Math.round(v*100)+"%";
[{key:"tone",label:"Тень"},{key:"grow",label:"Рост"},{key:"spikes",label:"Шипы"},{key:"drips",label:"Подтёки"},{key:"parts",label:"Части"},{key:"rag",label:"Шум"},
 {key:"pix",label:"Пиксель",fmt:v=>(1+Math.round(v*7))+" px"}]
  .forEach(k=>makeKnob($("knobs"),{label:k.label,value:state[k.key],fmt:k.fmt||pct,onInput:v=>{state[k.key]=v;renderSoon()}}));

setNote("Загрузи фото.");
})();
