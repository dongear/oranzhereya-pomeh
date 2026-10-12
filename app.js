(function(){
"use strict";

/* ---------- utils ---------- */
const $=id=>document.getElementById(id);
const TAU=Math.PI*2;
function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
const lerp=(a,b,t)=>a+(b-a)*t;
const angDiff=(a,b)=>((a-b)%TAU+3*Math.PI)%TAU-Math.PI;
function hashInts(a,b){let h=Math.imul((a|0)^0x9E3779B9,0x85EBCA6B)^(b|0);h=Math.imul(h^(h>>>13),0xC2B2AE35);return(h^(h>>>16))|0}
function wpick(rng,items){let s=0;items.forEach(i=>s+=Math.max(0,i[1]));let r=rng()*s;for(const i of items){r-=Math.max(0,i[1]);if(r<=0)return i[0]}return items[items.length-1][0]}
const easeOut=p=>1-Math.pow(1-p,3);
function fmtTime(s){const m=Math.floor(s/60),r=Math.floor(s%60);return m+":"+String(r).padStart(2,"0")}
const note=$("note");
function setNote(t,err){note.textContent=t;note.classList.toggle("err",!!err)}

function fft(re,im){
  const n=re.length;
  for(let i=1,j=0;i<n;i++){let bit=n>>1;for(;j&bit;bit>>=1)j^=bit;j^=bit;
    if(i<j){let t=re[i];re[i]=re[j];re[j]=t;t=im[i];im[i]=im[j];im[j]=t}}
  for(let len=2;len<=n;len<<=1){
    const ang=-2*Math.PI/len,wr=Math.cos(ang),wi=Math.sin(ang),half=len>>1;
    for(let i=0;i<n;i+=len){let cr=1,ci=0;
      for(let k=0;k<half;k++){const a=i+k,b=a+half;
        const tr=re[b]*cr-im[b]*ci,ti=re[b]*ci+im[b]*cr;
        re[b]=re[a]-tr;im[b]=im[a]-ti;re[a]+=tr;im[a]+=ti;
        const ncr=cr*wr-ci*wi;ci=cr*wi+ci*wr;cr=ncr}}}
}

/* ---------- analysis ---------- */
const NB=16,N=2048,MAXF=600;
const gE=(f,a,b)=>{let s=0;for(let k=a;k<b;k++)s+=f.bands[k];return s/(b-a)};

async function decodeToMono(arrayBuf){
  const AC=window.AudioContext||window.webkitAudioContext;
  const ac=new AC();
  let audio;
  try{audio=await new Promise((res,rej)=>{const p=ac.decodeAudioData(arrayBuf,res,rej);if(p&&p.then)p.then(res,rej)})}
  finally{try{ac.close()}catch(e){}}
  const len=audio.length,chs=audio.numberOfChannels,mono=new Float32Array(len);
  for(let c=0;c<chs;c++){const d=audio.getChannelData(c);for(let i=0;i<len;i++)mono[i]+=d[i]/chs}
  return {samples:mono,sr:audio.sampleRate};
}

function analyze(samples,sr){
  let mono=samples;
  if(mono.length<N){mono=new Float32Array(N);mono.set(samples)}
  const hop=Math.max(512,Math.floor((mono.length-N)/MAXF)||512);
  const win=new Float32Array(N);for(let i=0;i<N;i++)win[i]=0.5-0.5*Math.cos(2*Math.PI*i/(N-1));
  const nyq=sr/2,hiF=Math.min(16000,nyq*0.95);
  const edges=[];for(let b=0;b<=NB;b++)edges.push(Math.round(40*Math.pow(hiF/40,b/NB)/nyq*(N/2)));
  const re=new Float32Array(N),im=new Float32Array(N);
  let prev=null,seed=0;const frames=[];
  for(let start=0;start+N<=mono.length;start+=hop){
    let sum=0,zc=0;
    for(let i=0;i<N;i++){const s=mono[start+i];sum+=s*s;re[i]=s*win[i];im[i]=0;if(i&&((s>=0)!==(mono[start+i-1]>=0)))zc++}
    seed=(seed+Math.floor(Math.abs(mono[start+(N>>1)])*1e6))|0;
    fft(re,im);
    const half=N/2,mag=new Float32Array(half);
    let ms=0,cs=0,ls=0,flux=0;
    for(let k=1;k<half;k++){const m=Math.hypot(re[k],im[k]);mag[k]=m;ms+=m;cs+=m*k;ls+=Math.log(m+1e-9);
      if(prev){const d=m-prev[k];if(d>0)flux+=d}}
    const mean=ms/(half-1);
    const bands=new Float32Array(NB);
    for(let b=0;b<NB;b++){let a=Math.max(1,edges[b]),z=Math.max(a+1,edges[b+1]),s=0;for(let k=a;k<z&&k<half;k++)s+=mag[k];bands[b]=s/(z-a)}
    frames.push({rms:Math.sqrt(sum/N),cen:ms?(cs/ms)/half*nyq:0,flat:mean>0?Math.exp(ls/(half-1))/mean:0,zcr:zc/N,bands,flux});
    prev=mag;
  }
  if(!frames.length)return null;
  const maxR=Math.max(...frames.map(f=>f.rms),1e-9),maxF=Math.max(...frames.map(f=>f.flux),1e-9);
  const bandMax=new Float32Array(NB);let gMax=1e-9;
  frames.forEach(f=>{for(let b=0;b<NB;b++){bandMax[b]=Math.max(bandMax[b],f.bands[b]);gMax=Math.max(gMax,f.bands[b])}});
  frames.forEach(f=>{
    f.rms=f.rms/maxR;f.flux=f.flux/maxF;
    f.cen=clamp(f.cen/8000,0,1);f.flat=clamp(f.flat*3,0,1);f.zcr=clamp(f.zcr/0.3,0,1);
    for(let b=0;b<NB;b++){const v=f.bands[b];f.bands[b]=clamp(Math.sqrt(v/(bandMax[b]||1e-9))*0.6+Math.sqrt(v/gMax)*0.4,0,1)}
  });
  const fl=frames.map(f=>f.flux),m=fl.reduce((a,b)=>a+b,0)/fl.length,sd=Math.sqrt(fl.reduce((a,b)=>a+(b-m)*(b-m),0)/fl.length);
  let onsets=0;
  frames.forEach((f,i)=>{f.onset=f.flux>m+1.4*sd&&f.flux>=(fl[i-1]||0)&&f.flux>=(fl[i+1]||0);if(f.onset)onsets++});
  return summarize(frames,samples.length/sr,seed||12345,onsets);
}

function summarize(frames,duration,seed,onsets){
  const n=frames.length,avg=k=>frames.reduce((a,f)=>a+f[k],0)/n;
  const band=(a,b)=>frames.reduce((s,f)=>s+gE(f,a,b),0)/n;
  const avgRms=avg("rms");
  const dyn=Math.sqrt(frames.reduce((s,f)=>s+(f.rms-avgRms)*(f.rms-avgRms),0)/n);
  return {frames,duration,seed,onsets,onsetFrac:frames.filter(f=>f.onset).length/n,avgRms,avgCen:avg("cen"),avgFlat:avg("flat"),avgZcr:avg("zcr"),low:band(0,5),mid:band(5,11),high:band(11,16),dyn};
}

function combine(list){
  let frames=[].concat(...list.map(a=>a.frames));
  if(frames.length>MAXF){const o=[];for(let i=0;i<MAXF;i++)o.push(frames[Math.floor(i/MAXF*frames.length)]);frames=o}
  const seed=list.reduce((s,a)=>hashInts(s,a.seed),list[0].seed);
  return summarize(frames,list.reduce((s,a)=>s+a.duration,0),seed,list.reduce((s,a)=>s+a.onsets,0));
}

/* демо-звук: гул, колокольчики и шёпот шума */
function demoSound(){
  const sr=22050,len=sr*7,s=new Float32Array(len),r=mulberry32(77);
  for(let i=0;i<len;i++){const t=i/sr;s[i]=0.12*Math.sin(TAU*55*t+0.6*Math.sin(TAU*0.3*t))*(0.6+0.4*Math.sin(TAU*0.13*t))}
  const notes=[392,466,523,622,698,784,932];
  for(let k=0;k<14;k++){const t0=0.3+k*0.45+r()*0.2,f=notes[Math.floor(r()*notes.length)]*(r()<0.3?2:1),st=Math.floor(t0*sr);
    for(let i=0;i<sr*1.6&&st+i<len;i++){const t=i/sr;s[st+i]+=0.22*Math.exp(-t*3)*(Math.sin(TAU*f*t)+0.3*Math.sin(TAU*f*2.01*t))}}
  let lp=0;
  for(let i=0;i<len;i++){const t=i/sr,env=Math.pow(Math.max(0,Math.sin(TAU*t/3.5)),6);lp+=((r()*2-1)-lp)*0.08;s[i]+=lp*env*0.6}
  let pk=1e-9;for(let i=0;i<len;i++)pk=Math.max(pk,Math.abs(s[i]));
  for(let i=0;i<len;i++)s[i]*=0.8/pk;
  return {samples:s,sr};
}

/* ---------- палитры ---------- */
const PALETTES={
  paper:{name:"Белый",bg:"#FFFFFF",ink:"#111111",gray:"#8C8C8C"},
  night:{name:"Чёрный",bg:"#0B0B0B",ink:"#F0F0F0",gray:"#767676"}
};
function colors(key,G){
  const c=Object.assign({},PALETTES[key]);
  if(G.muts.has("pale"))c.ink=c.gray;
  return c;
}

/* ---------- гены ---------- */
const ARCHE_RU={tree:"ветвистое",weeper:"плакучее",vine:"вьющееся",fern:"папоротник",thistle:"колючее",sundew:"росянка",bulb:"луковичное"};
const MUTS={eyes:"пустоты",threads:"нити",twin:"двойник",spores:"споры",drips:"подтёки",pale:"бледность",thorns:"шипы",spiral:"спирали",broken:"надлом"};

function makeGenes(p){
  const A=p.A,r=mulberry32(hashInts(p.root,p.variant*7919+13)),gen=p.gen;
  const loud=clamp(A.avgRms*1.6,0,1),bright=clamp(A.avgCen*2.4,0,1),noisy=clamp(A.avgFlat*1.4,0,1);
  const zcr=clamp(A.avgZcr*1.5,0,1),low=clamp(A.low*1.3,0,1),mid=clamp(A.mid*1.3,0,1),high=clamp(A.high*1.3,0,1);
  const longness=clamp(Math.log2(1+A.duration)/6,0,1),pulse=clamp(A.onsetFrac/0.12,0,1);
  const j=()=>r()*0.55;
  const sc={tree:0.45+mid*0.5+loud*0.4+j(),weeper:(1-bright)*0.8+(1-loud)*0.5+j(),vine:longness*0.7+zcr*0.8+j(),
    fern:mid*0.4+(1-noisy)*0.7+j(),thistle:noisy*1.4+high*0.3+j(),sundew:pulse*0.9+high*0.5+j(),bulb:low*0.9+(1-mid)*0.3+j()};
  let arche="tree",best=-1;for(const k in sc)if(sc[k]>best){best=sc[k];arche=k}
  // подкормка иногда перерождает форму
  const mr=mulberry32(hashInts(A.seed,p.variant*131+gen));
  if(gen>1&&mr()<0.22){const ks=Object.keys(sc);arche=ks[Math.floor(mr()*ks.length)]}
  const muts=new Set();
  const mc=Math.min(4,Math.floor(r()*(1.2+noisy*1.6))+(gen>1?Math.floor(mr()*(gen*0.9)):0));
  const pool=[["eyes",0.6+noisy*0.4],["threads",0.8],["twin",0.5],["spores",0.6+high*0.6],["drips",0.6+(1-bright)*0.5],["pale",0.35],["thorns",noisy],["spiral",zcr+0.3],["broken",0.4]];
  for(let g=0;muts.size<mc&&g<50;g++)muts.add(wpick(g<20?r:mr,pool));
  const leafShape=arche==="thistle"?wpick(r,[["needle",1],["lobed",1]]):arche==="bulb"?"strap":arche==="fern"?(noisy>0.5?"lobed":"lance"):
    wpick(r,[["oval",0.3+mid*(1-noisy)],["lance",0.5],["heart",(1-noisy)*bright+0.15],["needle",noisy*0.8],["lobed",noisy*0.5+mid*0.3],["round",low*(1-noisy)*0.8]]);
  const flowerType=arche==="weeper"&&r()<0.75?"bell":arche==="thistle"?"orb":arche==="bulb"?wpick(r,[["spore",1],["orb",0.6],["bud",0.5]]):
    wpick(r,[["daisy",0.3+bright*0.7],["star",0.3+high*0.4],["tulip",mid*0.6],["bell",(1-bright)*0.6],["spore",high*0.5],["bud",(1-loud)*0.5],["orb",noisy*0.6]]);
  return {arche,loud,bright,noisy,zcr,low,mid,high,longness,pulse,gen,muts,
    height:clamp(0.55+loud*0.3+(r()-.5)*0.15+(gen-1)*0.04,0.45,0.97),
    stems:Math.min(3,1+Math.floor(r()*(1+A.dyn*6))),
    depth:clamp(2+(A.duration>6?1:0)+(A.duration>40?1:0)+Math.floor((gen-1)/2),2,4),
    branchAngle:0.35+bright*0.45+r()*0.2,
    curl:(0.004+zcr*0.02+r()*0.01)*(muts.has("spiral")?3.5:1),
    wobble:0.3+noisy*1.2,
    leafShape,leafSize:0.75+mid*0.6+r()*0.25,leafDensity:clamp(0.3+mid*0.6+r()*0.2,0,1),
    flowerType,flowerSize:0.75+loud*0.5+r()*0.3+(gen-1)*0.05,
    thorns:arche==="thistle"||muts.has("thorns"),
    hue:260+bright*140,
    geo:hashInts(p.root,p.variant*104729+gen*31+7)};
}

/* ---------- имена ---------- */
const GEN_P=["Strep","Susurr","Fragor","Murmur","Sonor","Tinnit","Crepit","Ulul","Fremit","Strid","Rumor","Querel","Echon","Vagit","Tremul","Sibil","Lament","Fluct","Noct","Lacrim"];
const GEN_S=[["aria","f"],["ella","f"],["ia","f"],["ula","f"],["anthus","m"],["ocarpus","m"],["odendron","n"],["ophyllum","n"],["opsis","f"],["ina","f"]];
const TRAITS={
  quiet:["tacitus","tacita","tacitum"],loud:["clamosus","clamosa","clamosum"],noisy:["raucus","rauca","raucum"],
  bright:["lucidus","lucida","lucidum"],dark:["obscurus","obscura","obscurum"],pulse:["pulsans","pulsans","pulsans"],
  long:["longaevus","longaeva","longaevum"],short:["brevis","brevis","breve"]
};

function makeNames(p,G){
  const r=mulberry32(hashInts(p.root,p.variant*17+3));
  const pre=GEN_P[Math.floor(r()*GEN_P.length)],suf=GEN_S[Math.floor(r()*GEN_S.length)];
  const sc=[["quiet",1-G.loud],["loud",G.loud],["noisy",G.noisy*1.2],["bright",G.bright],["dark",1-G.bright],["pulse",G.pulse*0.9],["long",G.longness],["short",1-G.longness]]
    .map(([k,v])=>[k,v+r()*0.35]).sort((a,b)=>b[1]-a[1]);
  const genus=pre+suf[0],epi=TRAITS[sc[0][0]][{m:0,f:1,n:2}[suf[1]]];
  let latin=genus+" "+epi;
  if(G.muts.has("eyes"))latin+=" var. vacua";else if(G.muts.has("drips"))latin+=" var. lacrimosa";
  return {latin,file:(genus+"_"+epi).toLowerCase()};
}

/* ---------- рисование: био-органика ---------- */
// Каждая часть тела — объём из затенённых шариков вдоль изогнутой оси (гладкая плоть, бугры,
// а если шарики реже — рифлёный позвоночник). Всё рисуется в сером, а paint() потом
// пропускает картинку через грязный порог, как ксерокопию фотографии.
let AM=1; // множитель прозрачности (для тени-двойника)
let LW=1; // единица толщины линии в координатах растения, пересчитывается под масштаб кадра
const K0="#000",WH="#fff";
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
// грязь: рыхлые точки и пятна, ложатся на теневую сторону
const GRIME=[];
function grime(ctx,x,y,r,v){
  if(!GRIME.length)for(let k=0;k<3;k++){const S=128,c=document.createElement("canvas");c.width=c.height=S;const g=c.getContext("2d"),rr=mulberry32(31+k);g.fillStyle="#000";
    for(let i=0;i<700;i++){const a=rr()*TAU,d=Math.pow(rr(),0.7)*S*0.48,px=S/2+Math.cos(a)*d,py=S/2+Math.sin(a)*d;g.globalAlpha=(1-d/(S*0.5))*0.9;g.beginPath();g.arc(px,py,0.6+rr()*rr()*4,0,TAU);g.fill()}
    for(let i=0;i<5;i++){g.globalAlpha=0.5;g.beginPath();g.ellipse(S/2+(rr()-.5)*S*0.5,S/2+(rr()-.5)*S*0.5,S*(0.04+rr()*0.1),S*(0.02+rr()*0.05),rr()*3,0,TAU);g.fill()}
    GRIME.push(c)}
  ctx.drawImage(GRIME[v%3],x-r,y-r,r*2,r*2);
}
// мягкий светлый блик без края: закрывает внутренние кольца, остаётся гладкий объём
let CORE=null;
function core(ctx,x,y,r){
  if(!CORE){const S=128;CORE=document.createElement("canvas");CORE.width=CORE.height=S;const g=CORE.getContext("2d"),gr=g.createRadialGradient(S/2,S/2,0,S/2,S/2,S/2);
    gr.addColorStop(0,"rgba(255,255,255,0.85)");gr.addColorStop(0.45,"rgba(235,235,235,0.7)");gr.addColorStop(0.75,"rgba(205,205,205,0.35)");gr.addColorStop(1,"rgba(200,200,200,0)");g.fillStyle=gr;g.fillRect(0,0,S,S)}
  if(r>0.3)ctx.drawImage(CORE,x-r*0.3-r*0.78,y-r*0.34-r*0.78,r*1.56,r*1.56);
}

function strokeLine(ctx,pts,p,col,w,alpha){
  const n=pts.length-1,L=p*n,k=Math.floor(L),fr=L-k;
  ctx.beginPath();ctx.moveTo(pts[0][0],pts[0][1]);
  for(let i=1;i<=k;i++)ctx.lineTo(pts[i][0],pts[i][1]);
  if(k<n&&fr>0){const a=pts[k],b=pts[k+1];ctx.lineTo(lerp(a[0],b[0],fr),lerp(a[1],b[1],fr))}
  ctx.globalAlpha=alpha*AM;ctx.strokeStyle=col;ctx.lineWidth=w;ctx.lineCap="round";ctx.lineJoin="round";ctx.stroke();
}
// дёрганая линия: каждая точка сдвинута поперёк направления
function jitter(pts,amp,r){
  return pts.map((p,i)=>{if(!i)return p;const q=pts[i-1],a=Math.atan2(p[1]-q[1],p[0]-q[0])+Math.PI/2,d=(r()-.5)*2*amp;
    return [p[0]+Math.cos(a)*d,p[1]+Math.sin(a)*d]});
}

// конечность: шарики вдоль оси, поверх прожилки и поры
function drawLimb(ctx,L,q){
  const n=L.balls.length,k=Math.ceil(n*q);if(!k)return;
  ctx.globalAlpha=AM;
  for(let i=0;i<k;i++){const b=L.balls[i];ball(ctx,b[0],b[1],b[2],b[3])}
  if(!L.ribbed)for(let i=0;i<k;i++){const b=L.balls[i];core(ctx,b[0],b[1],b[2])}
  for(const gm of L.grime){if(gm[4]>k)break;ctx.globalAlpha=gm[5]*AM;grime(ctx,gm[0],gm[1],gm[2],gm[3])}
  ctx.globalAlpha=AM;
  const f=k/n;
  if(L.veins.length){ctx.strokeStyle=K0;ctx.lineCap="round";ctx.lineJoin="round";ctx.globalAlpha=0.6*AM;ctx.lineWidth=LW*1.3;ctx.beginPath();
    L.veins.forEach(v=>{const m=Math.floor((v.length-1)*f);if(m<1)return;ctx.moveTo(v[0][0],v[0][1]);for(let i=1;i<=m;i++)ctx.lineTo(v[i][0],v[i][1])});ctx.stroke()}
  if(L.pores.length){ctx.fillStyle=K0;ctx.globalAlpha=0.75*AM;ctx.beginPath();
    L.pores.forEach(p=>{if(p[3]<=f){ctx.moveTo(p[0]+p[2],p[1]);ctx.arc(p[0],p[1],p[2],0,TAU)}});ctx.fill()}
  ctx.globalAlpha=AM;
}
// яйцо-кокон: вытянутый шар, трещины, тёмная щель у макушки
function drawEgg(ctx,e,s){
  if(s<=0.01)return;
  ctx.save();ctx.translate(e.x,e.y);ctx.rotate(e.a);ctx.scale(s,s);ctx.globalAlpha=AM;
  ctx.drawImage(ballSprite(e.dark),0,-e.Wd,e.L,e.Wd*2);
  ctx.strokeStyle=K0;ctx.lineCap="round";ctx.lineWidth=LW*1.4/s;ctx.globalAlpha=0.7*AM;ctx.beginPath();
  e.cracks.forEach(c=>{ctx.moveTo(c[0][0],c[0][1]);for(let i=1;i<c.length;i++)ctx.lineTo(c[i][0],c[i][1])});ctx.stroke();
  ctx.globalAlpha=AM;ctx.fillStyle=K0;ctx.beginPath();ctx.ellipse(e.L*0.88,0,e.L*0.07,e.Wd*0.32,0,0,TAU);ctx.fill();
  ctx.restore();
}
// рот или глазница: валик из шариков, зубы внутрь, чёрная глубина
function drawOrifice(ctx,o,s){
  const R=o.r*s;if(R<1)return;
  ctx.globalAlpha=AM;
  ball(ctx,o.x,o.y,R*1.1,true);
  for(let k=0;k<o.lips.length;k++){const a=o.rot+k/o.lips.length*TAU;ball(ctx,o.x+Math.cos(a)*R*0.74,o.y+Math.sin(a)*R*0.74,R*0.34*o.lips[k])}
  ctx.beginPath();ctx.ellipse(o.x,o.y,R*0.52,R*0.44,o.rot,0,TAU);ctx.fillStyle=K0;ctx.fill();
  if(o.teeth){ctx.beginPath();for(let k=0;k<o.teeth;k++){const a=o.rot+k/o.teeth*TAU+0.2,c=Math.cos(a),si=Math.sin(a),r0=R*0.5,r1=R*(0.22+0.12*(k%2));
    ctx.moveTo(o.x+c*r0-si*R*0.06,o.y+si*r0+c*R*0.06);ctx.lineTo(o.x+c*r1,o.y+si*r1);ctx.lineTo(o.x+c*r0+si*R*0.06,o.y+si*r0-c*R*0.06)}
    ctx.fillStyle="#d8d8d8";ctx.fill()}
  ctx.beginPath();ctx.ellipse(o.x-R*0.14,o.y-R*0.15,R*0.08,R*0.045,-0.6,0,TAU);ctx.fillStyle=WH;ctx.fill();
}
// комок плоти: шарики разного размера, нижние поверх верхних
function drawMass(ctx,m,q){const n=Math.ceil(m.balls.length*q);ctx.globalAlpha=AM;for(let i=0;i<n;i++){const b=m.balls[i];ball(ctx,b[0],b[1],b[2],b[3])}}

// какая часть тела вырастет на месте цветка
const BUD_KIND={daisy:"claws",star:"claws",tulip:"eggs",bud:"eggs",bell:"ribcage",orb:"spine",spore:"spine",eye:"orifice"};
const KINDS=["claws","eggs","ribcage","spine","orifice","mass"];

/* ---------- рост ---------- */
// X: {rag: грязь печати, drift: распад, splat: плотность деталей}, все 0..1
// рост почти случайный: конечности ползут в стороны, вниз, петлями; форма роста задаёт только характер
function buildPlant(plant,G,C,W,H,cap,X){
  const u=Math.min(W,H)/1000,wide=W>H,rng=mulberry32(G.geo),F=plant.A.frames;
  const ar=mulberry32(G.geo^0x5bd1e995);
  const fr=x=>F[clamp(Math.floor(x*F.length),0,F.length-1)];
  const PH=G.height*H*0.75,items=[],anchors=[],lines=[],spores=[];
  const bb={x0:Infinity,y0:Infinity,x1:-Infinity,y1:-Infinity};
  const ext=(x,y,r)=>{r=r||0;bb.x0=Math.min(bb.x0,x-r);bb.x1=Math.max(bb.x1,x+r);bb.y0=Math.min(bb.y0,y-r);bb.y1=Math.max(bb.y1,y+r)};
  const add=(L,t0,t1,f)=>{t0=clamp(t0,0,0.97);items.push({L,t0,t1:clamp(Math.max(t1,t0+0.02),0,1),f})};
  let limbCount=0,partIdx=0,flowers=0;

  // ось конечности: плавное блуждание, звук качает направление, конец может закрутиться
  function walk(x,y,a,len,w0,w1,o,r){
    r=r||rng;
    const n=Math.max(6,Math.round(len/(5*u))),sl=len/n,ph=[r()*TAU,r()*TAU,r()*TAU],f1=0.15+r()*0.25,f2=0.5+r()*0.6,wild=o.wild||0.6;
    const loopAt=o.loop?0.25+r()*0.4:-1,loopDir=r()<.5?-1:1;
    const pts=[[x,y]],angs=[a],ws=[w0];
    for(let i=1;i<=n;i++){
      const q=i/n,f=fr((o.f0||0)+(o.fs||0)*q);
      a+=(Math.sin(i*f1+ph[0])*0.05+Math.sin(i*f2+ph[1])*0.03)*wild*2+(f.bands[(i*5)%NB]-0.45)*0.09*wild+(r()-.5)*0.07*wild;
      if(o.grav)a+=angDiff(o.grav>0?Math.PI/2:-Math.PI/2,a)*Math.abs(o.grav);
      if(o.bend)a+=o.bend*Math.pow(q,3)*0.3;
      if(loopAt>=0&&q>loopAt&&q<loopAt+0.3)a+=loopDir*TAU/(0.3*n)*0.95;
      x+=Math.cos(a)*sl;y+=Math.sin(a)*sl;
      let w=lerp(w0,w1,Math.pow(q,0.85))*(1+0.22*Math.sin(i*0.3+ph[2])*(o.lumpy==null?1:o.lumpy))*(0.85+f.rms*0.3);
      if(o.beads)w*=0.7+0.5*Math.abs(Math.sin(i*o.beads));
      pts.push([x,y]);angs.push(a);ws.push(Math.max(0.6*u,w));
    }
    return {pts,angs,ws};
  }
  // объём вдоль оси
  function limb(P,t0,t1,o,r){
    r=r||rng;o=o||{};
    const ribbed=o.ribbed!=null?o.ribbed:r()<0.12+G.noisy*0.2,balls=[];
    let acc=0,cnt=0,sp=0.13;
    for(let i=0;i<P.pts.length;i++){
      if(i){acc+=Math.hypot(P.pts[i][0]-P.pts[i-1][0],P.pts[i][1]-P.pts[i-1][1])}
      if(i===0||acc>=sp*P.ws[i]){acc=0;cnt++;sp=ribbed?0.18+r()*0.32:0.1+r()*0.08;balls.push([P.pts[i][0],P.pts[i][1],P.ws[i],ribbed&&r()<0.2||o.dark]);ext(P.pts[i][0],P.pts[i][1],P.ws[i])}
    }
    const veins=[],pores=[];
    if(P.ws[0]>7*u&&!o.bare){
      const nv=r()<0.6?1+Math.floor(r()*2):0;
      for(let v=0;v<nv;v++){let off=(r()-.5)*0.8;const pts=[];
        for(let i=0;i<P.pts.length;i+=2){off=clamp(off+(r()-.5)*0.25,-0.7,0.7);const a=P.angs[i]+Math.PI/2;pts.push([P.pts[i][0]+Math.cos(a)*P.ws[i]*off,P.pts[i][1]+Math.sin(a)*P.ws[i]*off])}
        veins.push(pts)}
      const np=Math.floor(r()*P.pts.length*0.15*(0.5+G.noisy));
      for(let k=0;k<np;k++){const i=Math.floor(r()*P.pts.length),a=P.angs[i]+Math.PI/2,off=(r()-.5)*1.2;
        pores.push([P.pts[i][0]+Math.cos(a)*P.ws[i]*off,P.pts[i][1]+Math.sin(a)*P.ws[i]*off,P.ws[i]*(0.05+r()*0.07),i/P.pts.length])}
    }
    // пятна грязи на теневой стороне (свет сверху слева)
    const gr=[];balls.forEach((b,i)=>{if(r()<0.3+X.rag*0.4)gr.push([b[0]+b[2]*0.35,b[1]+b[2]*0.4,b[2]*(0.7+r()*0.7),Math.floor(r()*3),i,0.35+r()*0.5])});
    const L={balls,veins,pores,ribbed,grime:gr};
    add(2,t0,t1,(ctx,q)=>drawLimb(ctx,L,q));
    for(let i=3;i<P.pts.length;i+=5)anchors.push({x:P.pts[i][0],y:P.pts[i][1],w:P.ws[i],t:lerp(t0,t1,i/(P.pts.length-1))});
  }
  function mass(x,y,R,t,r,n){
    r=r||rng;const balls=[];n=n||Math.round(5+r()*8);
    for(let k=0;k<n;k++){const a=r()*TAU,d=Math.sqrt(r())*R*0.75,s=R*(0.25+r()*0.45);balls.push([x+Math.cos(a)*d,y+Math.sin(a)*d,s,r()<0.25]);ext(x+Math.cos(a)*d,y+Math.sin(a)*d,s)}
    balls.sort((p,q)=>p[1]-q[1]);
    const m={balls};add(2,t,t+0.12,(ctx,q)=>drawMass(ctx,m,easeOut(q)));
  }

  // часть тела на конце ветки. У каждой свой генератор, поэтому ручки меняют меру, а не форму
  function part(kind,x,y,a,R,t){
    const r=mulberry32(hashInts(G.geo,(partIdx++)*7919+11)),dens=0.5+X.splat*1.1;flowers++;
    if(r()<X.drift*0.8){const d=(20+r()*180)*u*X.drift,da=r()*TAU;x+=Math.cos(da)*d;y+=Math.sin(da)*d}else{r();r()}
    if(kind==="claws"){ // пальцы с когтями
      mass(x,y,R*0.55,t,r,5);
      const n=Math.max(2,Math.round((3+r()*3)*dens));
      for(let k=0;k<n;k++){const ca=a+(n>1?(k/(n-1)-0.5)*2:0)+(r()-.5)*0.4,side=ca<a?1:-1;
        const P=walk(x+Math.cos(ca)*R*0.3,y+Math.sin(ca)*R*0.3,ca,R*(1.3+r()*1.1),R*0.2,R*0.02,{wild:0.4,bend:side*(1.2+r()*1.5),lumpy:0.5,beads:r()<0.2?0.9:0},r);
        limb(P,t+0.03,t+0.15,{ribbed:r()<0.25,bare:true},r)}
    }else if(kind==="eggs"){ // кладка
      const n=Math.max(1,Math.round((1.5+r()*3)*dens));
      mass(x,y,R*0.5,t,r,4);
      for(let k=0;k<n;k++){const ea=a+(n>1?(k/(n-1)-0.5)*1.8:0)+(r()-.5)*0.4,L=R*(1.2+r()*0.8),Wd=L*(0.32+r()*0.12),cracks=[];
        for(let c=0;c<2+Math.floor(r()*3);c++){let px=L*(0.2+r()*0.5),py=(r()-.5)*Wd;const pts=[[px,py]];for(let j=0;j<5;j++){px+=L*0.08;py+=(r()-.5)*Wd*0.35;pts.push([px,clamp(py,-Wd*0.85,Wd*0.85)])}cracks.push(pts)}
        const e={x:x+Math.cos(ea)*R*0.2,y:y+Math.sin(ea)*R*0.2,a:ea,L,Wd,cracks,dark:r()<0.3};
        ext(e.x+Math.cos(ea)*L,e.y+Math.sin(ea)*L,Wd);ext(e.x,e.y,Wd);
        const t0=t+0.03*k;add(2,t0,t0+0.12,(ctx,q)=>drawEgg(ctx,e,easeOut(q)))}
    }else if(kind==="ribcage"){ // позвоночник и дуги рёбер
      const P=walk(x,y,a,R*2.2,R*0.3,R*0.12,{wild:0.3,beads:1.1,lumpy:0.2},r);
      limb(P,t,t+0.14,{ribbed:true,bare:true},r);
      const n=Math.max(2,Math.round((3+r()*3)*dens));
      for(let k=0;k<n;k++){const i=Math.round((k+1)/(n+1)*(P.pts.length-1)),p=P.pts[i];
        for(const s of[-1,1]){const ra=P.angs[i]+s*Math.PI/2,Rp=walk(p[0],p[1],ra,R*(1.6-k/n*0.6)*(0.8+r()*0.4),R*0.1,R*0.03,{wild:0.2,bend:-s*(1.5+r())*(angDiff(Math.PI/2,ra)>0?1:-1),lumpy:0.3},r);
          limb(Rp,t+0.05+k*0.01,t+0.18,{bare:true,ribbed:false},r)}}
    }else if(kind==="spine"){ // бусы позвонков, закрученные на конце
      const P=walk(x,y,a,R*3,R*0.4,R*0.1,{wild:0.5,beads:0.75,bend:(r()<.5?-1:1)*(2+r()*2),lumpy:0.2},r);
      limb(P,t,t+0.16,{ribbed:true,bare:true},r);
      const e=P.pts[P.pts.length-1];mass(e[0],e[1],R*0.35,t+0.15,r,4);
    }else if(kind==="orifice"){ // рот или глазница
      const n=Math.max(8,Math.round((9+r()*6)*(0.6+X.splat*0.6))),lips=[];for(let k=0;k<n;k++)lips.push(0.7+r()*0.6);
      const o={x,y,r:R*1.1,lips,rot:r()*TAU,teeth:r()<0.6?Math.round(6+r()*8):0};ext(x,y,R*1.4);
      add(2,t,t+0.14,(ctx,q)=>drawOrifice(ctx,o,easeOut(q)));
      const nc=Math.round(r()*3*dens);
      for(let k=0;k<nc;k++){const ca=r()*TAU,P=walk(x+Math.cos(ca)*R,y+Math.sin(ca)*R,ca,R*(0.9+r()),R*0.14,R*0.02,{wild:0.4,bend:(r()<.5?-1:1)*2},r);limb(P,t+0.08,t+0.18,{ribbed:true,bare:true},r)}
    }else mass(x,y,R*1.2,t,r,Math.round(7+r()*8*dens));
    if(G.muts.has("drips"))for(let k=0;k<2;k++){const dx=x+(r()-.5)*R,len=R*(2+r()*4);lines.push({pts:jitter([[dx,y],[dx,y+len*0.33],[dx,y+len*0.66],[dx,y+len]],(1+X.rag*3)*u,ar),t:t+0.1,w:1.4})}
  }
  function pickKind(type){
    type=type||G.flowerType;
    if(G.muts.has("eyes")&&rng()<0.4)return "orifice";
    return rng()<0.3?KINDS[Math.floor(rng()*KINDS.length)]:BUD_KIND[type]||"eggs";
  }

  // характер формы роста
  const AR={
    tree:{roots:1+Math.floor(rng()*G.stems),spread:0.6,grav:-0.02,len:0.7,kids:[3,2,1],wild:0.7},
    weeper:{roots:1+(rng()<.3?1:0),spread:0.4,grav:-0.03,cgrav:0.06,len:0.75,kids:[4,2,1],wild:0.6},
    vine:{roots:1+(rng()<.4?1:0),spread:0.8,grav:-0.008,len:1.8,kids:[2,1,0],wild:1.3,loop:true},
    fern:{roots:4+Math.round(G.mid*4),spread:2.4,grav:-0.008,len:0.75,kids:[1,0],wild:0.5,bend:2.2},
    thistle:{roots:2+Math.floor(rng()*3),spread:0.9,grav:-0.035,len:0.65,kids:[2,1],wild:0.4,spiky:true},
    sundew:{roots:7+Math.round(G.pulse*7),spread:3.4,grav:0,len:0.35,kids:[0],wild:0.6,term:"orifice"},
    bulb:{roots:2+Math.round(G.high*3),spread:1,grav:-0.015,len:0.85,kids:[1,0],wild:0.9,base:true}
  }[G.arche];
  const maxLvl=Math.min(AR.kids.length,G.depth);
  const spiral=G.muts.has("spiral");

  function grow(x,y,a,len,w,lvl,t0,t1,f0,fs){
    limbCount++;
    const P=walk(x,y,a,len,w,Math.max(2*u,w*(0.25+rng()*0.25)),{wild:AR.wild*(1+lvl*0.3)*(0.6+G.noisy*0.8),grav:lvl&&AR.cgrav?AR.cgrav:AR.grav,
      bend:(AR.bend||(rng()<0.3?2:0))*(rng()<.5?-1:1)*(spiral?2:1),loop:(AR.loop||spiral)&&rng()<0.5||rng()<0.12,f0,fs});
    limb(P,t0,t1);
    const n=P.pts.length-1,dt=t1-t0;
    // шипы и мелкие когти вдоль конечности
    if(AR.spiky||G.thorns)for(let i=4;i<n-2;i+=5+Math.floor(rng()*5)){const s=rng()<.5?-1:1,ca=P.angs[i]+s*(1+rng()*0.4),L=P.ws[i]*(1.5+rng()*2);
      const S=walk(P.pts[i][0],P.pts[i][1],ca,L,P.ws[i]*0.35,0.5*u,{wild:0.2,bend:-s*1.5},rng);limb(S,t0+dt*i/n,t0+dt*i/n+0.05,{bare:true,ribbed:false})}
    // ветвление: в случайных местах, в случайные стороны
    const nk=lvl<maxLvl&&limbCount<70?Math.round(AR.kids[lvl]*(0.5+rng())+G.mid*rng()):0;
    for(let k=0;k<nk;k++){
      const q=0.25+rng()*0.7,i=Math.min(n,Math.round(q*n)),ca=P.angs[i]+(rng()<.5?-1:1)*(0.35+rng()*1.4);
      mass(P.pts[i][0],P.pts[i][1],P.ws[i]*1.3,t0+dt*q,rng,3+Math.floor(rng()*3)); // сустав
      grow(P.pts[i][0],P.pts[i][1],ca,len*(0.35+rng()*0.5),P.ws[i]*(0.5+rng()*0.3),lvl+1,t0+dt*q,Math.min(0.9,t0+dt*q+dt*0.8),f0+fs*q,fs*(1-q));
    }
    // свисающие нити-отростки
    if(rng()<0.35){const i=Math.floor(rng()*n),S=walk(P.pts[i][0],P.pts[i][1],Math.PI/2+(rng()-.5)*0.6,len*(0.3+rng()*0.5),Math.max(1.5*u,P.ws[i]*0.15),0.8*u,{wild:0.5,grav:0.05},rng);
      limb(S,t0+dt*i/n,t0+dt*i/n+0.12,{bare:true,ribbed:rng()<0.5})}
    // наросты
    if(rng()<0.3){const i=Math.floor(rng()*n);mass(P.pts[i][0],P.pts[i][1],P.ws[i]*(1.5+rng()*1.5),t0+dt*i/n,rng)}
    // на конце — часть тела
    const tf=fr(f0+fs),R=(22+tf.rms*24)*u*G.flowerSize*Math.pow(0.85,lvl);
    if(rng()<(nk?0.35:0.85))part(AR.term&&rng()<0.6?AR.term:pickKind(),P.pts[n][0],P.pts[n][1],P.angs[n],R,Math.min(0.86,t1));
    // боковые части на всплесках звука
    for(let i=4;i<n-3;i++){const f=fr(f0+fs*i/n);if(f.onset&&rng()<0.18){const sa=P.angs[i]+(rng()<.5?-1:1)*(0.8+rng()*0.6);
      part(pickKind(),P.pts[i][0]+Math.cos(sa)*P.ws[i],P.pts[i][1]+Math.sin(sa)*P.ws[i],sa,R*0.6,Math.min(0.86,t0+dt*i/n+0.03))}}
  }

  const w0=(16+G.loud*22)*u,bx=W/2,by=H*0.8;
  if(AR.base)mass(bx,by,w0*2.6,0.02,rng,14);
  const nr=AR.roots+(rng()<0.45?1:0); // иногда лишний бродячий отросток в случайную сторону
  for(let k=0;k<nr;k++){
    const stray=k>=AR.roots,off=AR.roots>1?(k/(AR.roots-1)-0.5):0;
    const a=stray?rng()*TAU:-Math.PI/2+off*AR.spread+(rng()-.5)*0.6;
    grow(bx+(rng()-.5)*w0,by,a,PH*AR.len*(0.7+rng()*0.5)*(stray?0.6:1),w0*(stray?0.6:1)*(0.8+rng()*0.4),stray?1:0,0.05+k*0.04,0.6,0,1);
  }
  if(!flowers)part(pickKind(),bx,by-PH*0.5,-Math.PI/2,40*u,0.5);

  if(G.muts.has("threads")&&anchors.length){
    const nT=6+Math.floor(rng()*8);
    for(let k=0;k<nT;k++){const a=anchors[Math.floor(rng()*anchors.length)],len=(60+rng()*240)*u,sway=(rng()-.5)*16*u,pts=[];
      for(let i=0;i<=12;i++){const t=i/12;pts.push([a.x+Math.sin(t*Math.PI)*sway,a.y+t*len])}
      lines.push({pts:jitter(pts,(0.5+X.rag*3)*u,ar),t:a.t+0.04,w:1.1,end:true})}
  }
  // прямые подтёки вниз
  if(anchors.length){const nd=3+Math.round(G.noisy*6);
    for(let k=0;k<nd;k++){const a=anchors[Math.floor(rng()*anchors.length)],len=(60+rng()*260)*u;
      lines.push({pts:jitter([[a.x,a.y+a.w*0.8],[a.x,a.y+a.w+len*0.5],[a.x+(rng()-.5)*3*u,a.y+a.w+len]],(0.5+X.rag*2)*u,ar),t:a.t+0.05,w:1.2})}}
  lines.forEach(l=>l.pts.forEach(p=>ext(p[0],p[1])));

  if(G.muts.has("spores")){
    const ns=25+Math.round(G.high*40),pad=40*u;
    for(let k=0;k<ns;k++)spores.push([lerp(bb.x0-pad,bb.x1+pad,rng()),lerp(bb.y0-pad,bb.y1,Math.pow(rng(),1.4)),(2+rng()*6)*u,0.82+rng()*0.14]);
    spores.forEach(s=>ext(s[0],s[1]));
  }
  if(G.muts.has("broken")){ // надлом: рваная черта через всё растение
    const y0=lerp(bb.y0,bb.y1,0.3+rng()*0.4),tilt=(rng()-.5)*0.4*(bb.x1-bb.x0),x0=bb.x0-30*u,x1=bb.x1+30*u,pts=[];
    for(let i=0;i<=30;i++){const t=i/30;pts.push([lerp(x0,x1,t),y0+tilt*t])}
    lines.push({pts:jitter(pts,(2+X.rag*8)*u,ar),t:0.45,w:2.2});
  }
  // грязь: тёмные мазки и брызги вокруг тела
  const smudges=[];{const ns=Math.round(6+X.rag*14),size=Math.max(bb.x1-bb.x0,bb.y1-bb.y0);
    for(let k=0;k<ns;k++){const a=anchors.length?anchors[Math.floor(ar()*anchors.length)]:{x:bx,y:by};smudges.push([a.x+(ar()-.5)*size*0.15,a.y+(ar()-.5)*size*0.15,size*(0.03+ar()*0.09),0.1+ar()*0.25])}}

  // вписать рисунок в кадр
  const textSide=wide&&cap;
  const ax0=W*0.05,ax1=textSide?W*0.55:W*0.95,ay0=H*0.06,ay1=H*(cap&&!wide?0.86:0.94);
  const bw=Math.max(1,bb.x1-bb.x0),bh=Math.max(1,bb.y1-bb.y0);
  const s=Math.min((ax1-ax0)/bw,(ay1-ay0)/bh,1.8);
  const fit={s,tx:(ax0+ax1)/2-(bb.x0+bb.x1)/2*s,ty:(ay0+ay1)/2-(bb.y0+bb.y1)/2*s};

  add(0,0,0.5,(ctx,q)=>{smudges.forEach(m=>{const g=ctx.createRadialGradient(m[0],m[1],0,m[0],m[1],m[2]);g.addColorStop(0,"rgba(0,0,0,"+(m[3]*q).toFixed(3)+")");g.addColorStop(1,"rgba(0,0,0,0)");
    ctx.globalAlpha=AM;ctx.fillStyle=g;ctx.fillRect(m[0]-m[2],m[1]-m[2],m[2]*2,m[2]*2)})});
  lines.forEach(l=>add(1,l.t,l.t+0.14,(ctx,q)=>{strokeLine(ctx,l.pts,q,K0,LW*l.w*1.3,1);
    if(l.end&&q>=1){const e=l.pts[l.pts.length-1];ctx.globalAlpha=AM;ball(ctx,e[0],e[1],5*u,true)}}));
  if(spores.length)add(4,0.8,1,(ctx,q)=>{const T=lerp(0.8,1,q);ctx.globalAlpha=AM;spores.forEach(p=>{if(T>=p[3])ball(ctx,p[0],p[1],p[2],true)})});

  items.sort((a,b)=>a.L-b.L||a.t0-b.t0);
  return {ops:items,u,W,H,fit,lw:u/s,cx:(bb.x0+bb.x1)/2,bx:W/2,twin:G.muts.has("twin"),flowers,cap,textSide};
}

/* ---------- подпись ---------- */
function wrapText(ctx,text,maxW){const words=text.split(" "),lines=[];let line="";
  words.forEach(w=>{const t=line?line+" "+w:w;if(ctx.measureText(t).width>maxW&&line){lines.push(line);line=w}else line=t});if(line)lines.push(line);return lines}

function drawCaption(ctx,M,p,C,info){
  const {W,H}=M,serif='Georgia, "Times New Roman", serif',no=String(info.id).padStart(3,"0");
  ctx.save();ctx.globalAlpha=p;ctx.fillStyle=C.ink;ctx.textBaseline="alphabetic";
  if(M.textSide){
    const x=W*0.6,maxW=W*0.34;let y=H*0.24;
    ctx.textAlign="left";
    ctx.font=Math.round(H*0.017)+"px "+serif;ctx.globalAlpha=p*0.6;
    ctx.fillText("ЦВЕТОЧНЫЙ МАГАЗИН «ПОМЕХА»   № "+no,x,y);
    y+=H*0.09;ctx.globalAlpha=p;
    ctx.font="italic "+Math.round(H*0.056)+"px "+serif;
    wrapText(ctx,info.latin,maxW).forEach(l=>{ctx.fillText(l,x,y);y+=H*0.062});
    y+=H*0.03;ctx.font=Math.round(H*0.02)+"px "+serif;ctx.globalAlpha=p*0.7;
    info.facts.forEach(f=>{wrapText(ctx,f,maxW).forEach(l=>{ctx.fillText(l,x,y);y+=H*0.032})});
  }else{
    ctx.textAlign="center";
    ctx.font="italic "+Math.round(H*0.032)+"px "+serif;ctx.fillText(info.latin,M.bx,H*0.945);
    ctx.font=Math.round(H*0.014)+"px "+serif;ctx.globalAlpha=p*0.6;
    ctx.fillText("№ "+no,M.bx,H*0.972);
  }
  ctx.restore();
}

/* ---------- голос ---------- */
const LAYER=[1,0.75,1.5,0.5,1.25,0.66];
function voiceParams(p,G){
  const r=mulberry32(hashInts(p.root,p.variant*31+p.gen*977+5));
  return {rate:clamp(0.5+G.bright*0.35+(r()-.5)*0.12-(p.gen-1)*0.04,0.38,1),cutoff:600+G.bright*5200+r()*800,q:0.7+G.noisy*6,
    delay:0.17+r()*0.45,fb:clamp(0.25+G.noisy*0.3+(p.gen-1)*0.07,0,0.72),wet:clamp(0.35+(1-G.loud)*0.3+(p.gen-1)*0.07,0,0.88),
    tremHz:1.5+G.zcr*7,tremDepth:clamp(G.noisy*0.6,0,0.6),wob:0.004+(G.muts.has("spiral")?0.02:0)+r()*0.008,wobHz:0.15+r()*0.5,
    reverse:r()<0.2||G.muts.has("broken"),irLen:2.5+G.low*2.5,seed:hashInts(p.root,99)};
}
function voicePlan(p,V){
  let end=0;
  const items=p.sounds.map((s,k)=>{const rate=V.rate*LAYER[k%LAYER.length],dur=s.samples.length/s.sr,play=Math.min(dur,40*rate),out=play/rate,st=k*1.3;
    end=Math.max(end,st+out);return {s,rate,play,out,st,gain:Math.pow(0.72,k)}});
  return {items,length:end+V.irLen+V.fb*3+0.5};
}
function impulse(ctx,V){
  const sr=ctx.sampleRate,len=Math.floor(sr*V.irLen),b=ctx.createBuffer(2,len,sr),r=mulberry32(V.seed);
  for(let c=0;c<2;c++){const d=b.getChannelData(c);for(let i=0;i<len;i++)d[i]=(r()*2-1)*Math.pow(1-i/len,2.6)}
  return b;
}
const echoSend=fb=>Math.min(0.8,fb*1.1);
const masterGain=V=>0.9/(1+V.wet*0.45+V.fb*0.7);
function buildVoice(ctx,p,V,plan){
  const t0=ctx.currentTime+0.05,nodes=[],srcs=[];
  const master=ctx.createGain();master.gain.value=masterGain(V);
  // компрессор и мягкий ограничитель, чтобы эхо и простор не перегружали звук
  const comp=ctx.createDynamicsCompressor(),clip=ctx.createWaveShaper(),curve=new Float32Array(1024);
  for(let i=0;i<1024;i++){const x=i/511.5-1;curve[i]=Math.tanh(x*1.4)/Math.tanh(1.4)*0.95}
  clip.curve=curve;master.connect(comp);comp.connect(clip);clip.connect(ctx.destination);
  const filt=ctx.createBiquadFilter();filt.type="lowpass";filt.frequency.value=V.cutoff;filt.Q.value=V.q;
  const trem=ctx.createGain();trem.gain.value=1-V.tremDepth/2;
  const lfo=ctx.createOscillator();lfo.frequency.value=V.tremHz;const lg=ctx.createGain();lg.gain.value=V.tremDepth/2;lfo.connect(lg);lg.connect(trem.gain);
  filt.connect(trem);
  const dry=ctx.createGain();dry.gain.value=1-V.wet*0.6;trem.connect(dry);dry.connect(master);
  const conv=ctx.createConvolver();conv.buffer=impulse(ctx,V);const wg=ctx.createGain();wg.gain.value=V.wet;trem.connect(conv);conv.connect(wg);wg.connect(master);
  const dl=ctx.createDelay(2);dl.delayTime.value=V.delay;const fb=ctx.createGain();fb.gain.value=V.fb;const dlf=ctx.createBiquadFilter();dlf.type="lowpass";dlf.frequency.value=2500;
  trem.connect(dl);dl.connect(dlf);dlf.connect(fb);fb.connect(dl);const dg=ctx.createGain();dg.gain.value=echoSend(V.fb);dlf.connect(dg);dg.connect(master);dg.connect(conv);
  const wl=ctx.createOscillator();wl.frequency.value=V.wobHz;
  plan.items.forEach((it,k)=>{
    const s=it.s,n=Math.min(s.samples.length,Math.floor(it.play*s.sr)),buf=ctx.createBuffer(1,n,s.sr),d=buf.getChannelData(0);
    d.set(s.samples.subarray(0,n));
    if(V.reverse&&k===0)d.reverse();
    // мягкое начало и конец прямо в данных, чтобы скорость можно было крутить на ходу
    const fi=Math.min(n>>2,Math.floor(s.sr*0.02)),fo=Math.min(n>>2,Math.floor(s.sr*0.3));
    for(let i=0;i<fi;i++)d[i]*=i/fi;for(let i=0;i<fo;i++)d[n-1-i]*=i/fo;
    const src=ctx.createBufferSource();src.buffer=buf;src.playbackRate.value=it.rate;
    const wg2=ctx.createGain();wg2.gain.value=it.rate*V.wob;wl.connect(wg2);wg2.connect(src.playbackRate);
    const g=ctx.createGain();g.gain.value=it.gain;
    src.connect(g);g.connect(filt);src.start(t0+it.st);nodes.push(src);srcs.push({src,wg:wg2,layer:LAYER[k%LAYER.length]});
  });
  lfo.start(t0);wl.start(t0);nodes.push(lfo,wl);
  return {nodes,srcs,master,filt,trem,lg,dry,wg,fb,dg};
}
// поменять параметр звучащего голоса
function tweakVoice(v,V,ctx){
  const t=ctx.currentTime,k=0.04;
  v.srcs.forEach(s=>{s.src.playbackRate.setTargetAtTime(V.rate*s.layer,t,k);s.wg.gain.setTargetAtTime(V.rate*s.layer*V.wob,t,k)});
  v.filt.frequency.setTargetAtTime(V.cutoff,t,k);
  v.fb.gain.setTargetAtTime(V.fb,t,k);v.dg.gain.setTargetAtTime(echoSend(V.fb),t,k);
  v.wg.gain.setTargetAtTime(V.wet,t,k);v.dry.gain.setTargetAtTime(1-V.wet*0.6,t,k);
  v.master.gain.setTargetAtTime(masterGain(V),t,k);
  v.lg.gain.setTargetAtTime(V.tremDepth/2,t,k);v.trem.gain.setTargetAtTime(1-V.tremDepth/2,t,k);
}
function encodeWav(buf){
  const ch=buf.numberOfChannels,len=buf.length,sr=buf.sampleRate,data=new DataView(new ArrayBuffer(44+len*ch*2));
  const w=(o,s)=>{for(let i=0;i<s.length;i++)data.setUint8(o+i,s.charCodeAt(i))};
  w(0,"RIFF");data.setUint32(4,36+len*ch*2,true);w(8,"WAVE");w(12,"fmt ");data.setUint32(16,16,true);data.setUint16(20,1,true);data.setUint16(22,ch,true);
  data.setUint32(24,sr,true);data.setUint32(28,sr*ch*2,true);data.setUint16(32,ch*2,true);data.setUint16(34,16,true);w(36,"data");data.setUint32(40,len*ch*2,true);
  const chans=[];for(let c=0;c<ch;c++)chans.push(buf.getChannelData(c));
  let o=44;for(let i=0;i<len;i++)for(let c=0;c<ch;c++){const v=clamp(chans[c][i],-1,1);data.setInt16(o,v<0?v*0x8000:v*0x7FFF,true);o+=2}
  return new Blob([data],{type:"audio/wav"});
}

/* ---------- состояние и отрисовка ---------- */
const state={palette:"paper",format:"square",caption:true,transparent:false,mode:"plant",rag:0.5,drift:0.15,splat:0.5,pix:0.43};
const plants=[];let current=null,uid=0,busy=false,model=null,anim=null;
const cv=$("cv"),frame=$("frame");
const reduceMotion=window.matchMedia&&window.matchMedia("(prefers-reduced-motion: reduce)").matches;

function prepare(p){
  p.G=makeGenes(p);p.names=makeNames(p,p.G);p.V=voiceParams(p,p.G);
}
function makeModel(p){
  const W=state.format==="wide"?2400:2000,H=state.format==="wide"?1350:2000;
  const C=colors(state.palette,p.G);
  const M=buildPlant(p,p.G,C,W,H,state.caption,{rag:state.rag,drift:state.drift,splat:state.splat});
  M.C=C;M.plant=p;
  if(state.caption){
    const G=p.G,facts=["Форма: "+ARCHE_RU[G.arche],"Бутонов: "+M.flowers,"Поколение: "+G.gen];
    if(G.muts.size)facts.push("Мутации: "+[...G.muts].map(k=>MUTS[k]).join(", "));
    const info={id:p.id,latin:p.names.latin,facts};
    M.ops.push({L:6,t0:0.72,t1:1,f:(ctx,q)=>drawCaption(ctx,M,q,C,info)});
  }
  return M;
}

// грязный порог, как ксерокопия фотографии: пиксель чёрный, если это глубокая тень
// или если он темнее своего окружения; пятнистый шум рвёт линии и даёт крошку в полутонах
let NZ=null,OFF=null,SMALL=null,MID=null,BLR=null;
function noiseTile(){
  if(NZ)return NZ;
  const S=512,C=32,a=new Uint8Array(S*S),r=mulberry32(5),c=new Float32Array(C*C);
  for(let i=0;i<c.length;i++)c[i]=r();
  for(let y=0;y<S;y++)for(let x=0;x<S;x++){const fx=x/S*C,fy=y/S*C,x0=Math.floor(fx),y0=Math.floor(fy),tx=fx-x0,ty=fy-y0,
    g=(i,j)=>c[(j%C)*C+(i%C)],v=lerp(lerp(g(x0,y0),g(x0+1,y0),tx),lerp(g(x0,y0+1),g(x0+1,y0+1),tx),ty);
    a[y*S+x]=Math.round(clamp(v*0.55+r()*0.45,0,1)*255)}
  return NZ=a;
}
const hexRGB=h=>{const m=/^#?([0-9a-f]{6})$/i.exec(h);const v=m?parseInt(m[1],16):0;return [v>>16&255,v>>8&255,v&255]};
const mk=()=>document.createElement("canvas");
// размер пикселя: ручка 0..1 → 1..8 точек холста
const pixSize=()=>1+Math.round(state.pix*7);
function paint(M,T){
  const px=pixSize(),sc=1/px,w=Math.max(8,Math.round(M.W*sc)),h=Math.max(8,Math.round(M.H*sc));
  if(!OFF){OFF=mk();SMALL=mk();MID=mk();BLR=mk()}
  if(OFF.width!==w||OFF.height!==h){OFF.width=w;OFF.height=h;BLR.width=w;BLR.height=h}
  const o=OFF.getContext("2d",{willReadFrequently:true});
  o.setTransform(1,0,0,1,0,0);o.globalAlpha=1;o.fillStyle=WH;o.fillRect(0,0,w,h);
  LW=M.lw*Math.max(1,px*0.7); // тонкие линии не должны пропасть при крупном пикселе
  o.setTransform(M.fit.s*sc,0,0,M.fit.s*sc,M.fit.tx*sc,M.fit.ty*sc);
  if(M.twin){o.save();o.translate(2*M.cx+M.u*70,-M.u*24);o.scale(-1,1);AM=0.3;drawOps(o,M.ops,T,x=>x.L<6);o.restore();AM=1}
  drawOps(o,M.ops,T,x=>x.L<6);
  o.setTransform(1,0,0,1,0,0);
  // среднее по окрестности: уменьшить в два шага и растянуть обратно со сглаживанием
  MID.width=Math.max(4,Math.round(w/4));MID.height=Math.max(4,Math.round(h/4));SMALL.width=Math.max(2,Math.round(w/14));SMALL.height=Math.max(2,Math.round(h/14));
  const mc=MID.getContext("2d"),smc=SMALL.getContext("2d"),bc=BLR.getContext("2d",{willReadFrequently:true});
  mc.imageSmoothingQuality=smc.imageSmoothingQuality=bc.imageSmoothingQuality="high";
  mc.drawImage(OFF,0,0,MID.width,MID.height);smc.drawImage(MID,0,0,SMALL.width,SMALL.height);
  bc.clearRect(0,0,w,h);bc.drawImage(SMALL,0,0,w,h);
  const img=o.getImageData(0,0,w,h),d=img.data,mean=bc.getImageData(0,0,w,h).data,N=noiseTile();
  const gray=new Uint8Array(w*h);for(let k=0,i=0;k<gray.length;k++,i+=4)gray[k]=d[i];
  const g=state.rag,bias=M.plant.G.muts.has("pale")?35:0,ink=hexRGB(M.C.ink),bg=hexRGB(M.C.bg),tr=state.transparent;
  const deep=48+g*35,edge=4+(1-g)*6,nAmp=16+g*30,shake=0.4+g*1.4;
  for(let y=0,i=0,k=0;y<h;y++){const row=(y&511)<<9,row2=((y+211)&511)<<9;
    for(let x=0;x<w;x++,i+=4,k++){
      // пиксельный шум «трясёт» картинку: края рвутся лесенкой, круги перестают быть кругами
      const sx=clamp(x+Math.round((N[row|((x+97)&511)]-128)/128*shake),0,w-1),sy=clamp(y+Math.round((N[row2|((x+31)&511)]-128)/128*shake),0,h-1);
      const v=gray[sy*w+sx]+bias,nz=(N[row|(x&511)]-128)/128,m=mean[i];
      const on=v<254&&(v<deep+nz*40||v-m<-edge+nz*nAmp*0.5||(v<242&&nz<-0.62+(242-v)/105));
      if(tr){d[i]=ink[0];d[i+1]=ink[1];d[i+2]=ink[2];d[i+3]=on?255:0}
      else{const c=on?ink:bg;d[i]=c[0];d[i+1]=c[1];d[i+2]=c[2];d[i+3]=255}}}
  o.putImageData(img,0,0);
  if(cv.width!==M.W||cv.height!==M.H){cv.width=M.W;cv.height=M.H}
  const ctx=cv.getContext("2d");
  ctx.setTransform(1,0,0,1,0,0);ctx.globalAlpha=1;ctx.clearRect(0,0,M.W,M.H);
  ctx.imageSmoothingEnabled=false;ctx.drawImage(OFF,0,0,M.W,M.H);ctx.imageSmoothingEnabled=true;
  drawOps(ctx,M.ops,T,x=>x.L>=6);
  ctx.globalAlpha=1;
}
function drawOps(ctx,ops,T,filter){
  for(const o of ops){if(filter&&!filter(o))continue;if(T<=o.t0)continue;
    const q=Math.min(1,(T-o.t0)/(o.t1-o.t0));ctx.globalAlpha=AM;o.f(ctx,q)}
}

function show(p,animate){
  anim=null;
  model=makeModel(p);
  if(typeof syncVoiceKnobs==="function")syncVoiceKnobs(p);
  frame.classList.toggle("checker",state.transparent);
  updatePassport(p);
  if(!animate||reduceMotion){paint(model,1);afterGrow(p);return}
  const M=model,start=performance.now(),dur=4200;
  // кадр по requestAnimationFrame, с запасным таймером, если кадры не приходят
  const next=cb=>{let done=false;const f=()=>{if(done)return;done=true;cb(performance.now())};requestAnimationFrame(f);setTimeout(f,60)};
  const step=now=>{if(model!==M)return;const T=Math.min(1,(now-start)/dur);paint(M,T);
    if(T<1)next(step);else{anim=null;afterGrow(p)}};
  anim=true;next(step);
}
function afterGrow(p){
  const t=document.createElement("canvas"),s=280;t.width=s;t.height=s;
  const c=t.getContext("2d"),k=Math.max(s/cv.width,s/cv.height);
  c.fillStyle=model.C.bg;c.fillRect(0,0,s,s);
  c.drawImage(cv,(s-cv.width*k)/2,(s-cv.height*k)/2,cv.width*k,cv.height*k);
  try{p.thumb=t.toDataURL("image/jpeg",0.82)}catch(e){}
  renderShelf();
}

function updatePassport(p){
  const G=p.G;
  $("pLatin").textContent=p.names.latin;
  $("pMeta").textContent="№ "+String(p.id).padStart(3,"0")+" · поколение "+G.gen;
  const rows=[["Звук",p.sounds.map(s=>s.label).join(" + ")],["Длительность",fmtTime(p.A.duration)],["Форма",ARCHE_RU[G.arche]],
    ["Бутонов",String(model.flowers)],["Мутации",G.muts.size?[...G.muts].map(k=>MUTS[k]).join(", "):"нет"]];
  const dl=$("stats");dl.innerHTML="";
  rows.forEach(([k,v])=>{const dt=document.createElement("dt"),dd=document.createElement("dd");dt.textContent=k;dd.textContent=v;dl.append(dt,dd)});
}

function renderShelf(){
  const box=$("shelf");box.innerHTML="";
  plants.forEach(p=>{
    const b=document.createElement("button");b.className="card";b.setAttribute("aria-current",p===current);
    if(p.thumb){const i=document.createElement("img");i.src=p.thumb;i.alt="";b.append(i)}
    const n=document.createElement("span");n.textContent=p.names.latin;
    const s=document.createElement("small");s.textContent="№ "+String(p.id).padStart(3,"0")+" · п. "+p.gen;
    b.append(n,s);
    b.addEventListener("click",()=>{if(busy||p===current)return;stopVoice();current=p;show(p,false);setNote("")});
    box.append(b);
  });
}

/* ---------- звук на входе ---------- */
async function handleSound(blob,label){
  if(!blob||busy)return;
  busy=true;setBusyUI(true);stopVoice();
  setNote("Анализ…");
  try{
    const {samples,sr}=await decodeToMono(await blob.arrayBuffer());
    const A=analyze(samples,sr);
    if(!A)throw new Error("short");
    const sound={samples,sr,label,A};
    if(state.mode==="feed"&&current){
      if(current.sounds.length>=6){setNote("Максимум шесть звуков. Начни новое.",true);return}
      const p=current;p.sounds.push(sound);p.gen++;p.A=combine(p.sounds.map(s=>s.A));
      const oldArche=p.G.arche;prepare(p);show(p,true);
      setNote("Поколение "+p.gen+"."+(p.G.arche!==oldArche?" Форма сменилась.":""));
    }else{
      const p={id:++uid,sounds:[sound],root:A.seed,variant:0,gen:1,A};
      prepare(p);plants.unshift(p);current=p;show(p,true);
      setNote("");
    }
  }catch(err){
    setNote("Не удалось прочитать звук. Нужен mp3 или wav длиннее 0,5 с.",true);
  }finally{busy=false;setBusyUI(false)}
}
function setBusyUI(b){["again","save","saveVoice"].forEach(id=>$(id).disabled=b);$("drop").style.opacity=b?0.5:""}

$("file").addEventListener("change",e=>{const f=e.target.files[0];if(f)handleSound(f,f.name);e.target.value=""});
const drop=$("drop");
["dragenter","dragover"].forEach(t=>drop.addEventListener(t,e=>{e.preventDefault();drop.classList.add("over")}));
["dragleave","drop"].forEach(t=>drop.addEventListener(t,e=>{e.preventDefault();drop.classList.remove("over")}));
drop.addEventListener("drop",e=>{const f=e.dataTransfer&&e.dataTransfer.files[0];if(f)handleSound(f,f.name)});

// микрофон
const micBtn=$("mic");let rec=null;
micBtn.addEventListener("click",async()=>{
  if(rec){rec.stop();return}
  if(busy)return;
  if(!navigator.mediaDevices||!navigator.mediaDevices.getUserMedia||!window.MediaRecorder){setNote("Браузер не поддерживает запись.",true);return}
  let stream;
  try{stream=await navigator.mediaDevices.getUserMedia({audio:true})}
  catch(e){setNote("Нет доступа к микрофону.",true);return}
  const chunks=[];rec=new MediaRecorder(stream);
  rec.ondataavailable=e=>{if(e.data&&e.data.size)chunks.push(e.data)};
  const t0=Date.now();
  const tick=setInterval(()=>{const s=(Date.now()-t0)/1000;micBtn.textContent="Стоп · "+fmtTime(s);if(s>=20&&rec&&rec.state==="recording")rec.stop()},250);
  rec.onstop=()=>{clearInterval(tick);stream.getTracks().forEach(t=>t.stop());rec=null;
    micBtn.textContent="Запись";micBtn.classList.remove("rec");
    const blob=new Blob(chunks,{type:(chunks[0]&&chunks[0].type)||"audio/webm"});handleSound(blob,"запись с микрофона")};
  rec.start();micBtn.classList.add("rec");micBtn.textContent="Стоп · 0:00";
  setNote("Запись, до 20 с.");
});

/* ---------- голос: воспроизведение ---------- */
let AC=null,voice=null,voiceTimer=null;
const listenBtn=$("listen");
function stopVoice(){
  if(voice){voice.nodes.forEach(n=>{try{n.stop()}catch(e){}});try{voice.master.disconnect()}catch(e){}voice=null}
  clearTimeout(voiceTimer);listenBtn.textContent="Слушать";frame.classList.remove("singing");
}
function startVoice(){
  if(!current)return;
  const C=window.AudioContext||window.webkitAudioContext;
  if(!AC)AC=new C();if(AC.state==="suspended")AC.resume();
  const V=current.V,plan=voicePlan(current,V),v=buildVoice(AC,current,V,plan);
  voice=v;
  // когда все слои доиграли, ждём хвост эха и выключаем
  let left=v.srcs.length;
  v.srcs.forEach(s=>s.src.onended=()=>{if(--left===0&&voice===v)voiceTimer=setTimeout(stopVoice,(V.irLen+V.fb*3)*1000)});
  listenBtn.textContent="Стоп";frame.classList.add("singing");
}
listenBtn.addEventListener("click",()=>{if(voice)stopVoice();else startVoice()});

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
$("save").addEventListener("click",async()=>{
  if(!current)return;
  if(anim){anim=null;model=makeModel(current);paint(model,1);afterGrow(current)}
  const blob=await new Promise(r=>cv.toBlob(r,"image/png"));
  saveBlob(blob,current.names.file+".png","Картинка сохранена.");
});
$("saveVoice").addEventListener("click",async()=>{
  if(!current||busy)return;
  const p=current,V=p.V,plan=voicePlan(p,V);
  const OAC=window.OfflineAudioContext||window.webkitOfflineAudioContext;
  if(!OAC){setNote("Браузер не умеет сохранять звук.",true);return}
  busy=true;setBusyUI(true);setNote("Запись WAV…");
  try{
    const sr=44100,ctx=new OAC(2,Math.ceil(plan.length*sr),sr);
    buildVoice(ctx,p,V,plan);
    const buf=await new Promise((res,rej)=>{ctx.oncomplete=e=>res(e.renderedBuffer);const r=ctx.startRendering();if(r&&r.then)r.then(res,rej)});
    busy=false;setBusyUI(false);
    await saveBlob(encodeWav(buf),p.names.file+"_golos.wav","Голос сохранён.");
  }catch(e){setNote("Не удалось записать WAV.",true)}
  finally{busy=false;setBusyUI(false)}
});

/* ---------- настройки ---------- */
const palWrap=$("palettes");
Object.entries(PALETTES).forEach(([k,p])=>{
  const b=document.createElement("button");b.dataset.v=k;b.setAttribute("aria-pressed",k===state.palette);
  b.textContent=p.name;palWrap.append(b);
});
function bindSeg(el,key,after){el.addEventListener("click",e=>{const b=e.target.closest("button");if(!b||b.disabled)return;
  state[key]=b.dataset.v;el.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",x===b));after()})}
const redraw=()=>{if(current)show(current,false)};
bindSeg(palWrap,"palette",redraw);bindSeg($("formats"),"format",redraw);
bindSeg($("modes"),"mode",()=>{$("dropTitle").textContent=state.mode==="feed"?"Звук для подкормки":"Загрузить звук";
  setNote(state.mode==="feed"?"Следующий звук подкормит этот образец.":"Следующий звук станет новым образцом.")});
$("caption").addEventListener("change",e=>{state.caption=e.target.checked;redraw()});
$("transparent").addEventListener("change",e=>{state.transparent=e.target.checked;redraw()});
$("again").addEventListener("click",()=>{if(!current||busy)return;stopVoice();current.variant++;prepare(current);show(current,true);
  setNote("")});

/* ---------- ручки ---------- */
const SVGNS="http://www.w3.org/2000/svg",A0=-135,A1=135;
function arcD(a0,a1){const r=19,p=a=>{const t=(a-90)*Math.PI/180;return (24+Math.cos(t)*r).toFixed(2)+" "+(24+Math.sin(t)*r).toFixed(2)};
  return "M "+p(a0)+" A "+r+" "+r+" 0 "+(a1-a0>180?1:0)+" 1 "+p(a1)}
// o: {label,min,max,log,fmt,onInput}; внутри ручка живёт в 0..1
function makeKnob(box,o){
  const el=document.createElement("div");el.className="knob";
  const dial=document.createElement("div");dial.className="knob-dial";dial.tabIndex=0;dial.setAttribute("role","slider");dial.setAttribute("aria-label",o.label);
  dial.setAttribute("aria-valuemin","0");dial.setAttribute("aria-valuemax","100");
  const svg=document.createElementNS(SVGNS,"svg");svg.setAttribute("viewBox","0 0 48 48");
  const mk=(tag,cls)=>{const e=document.createElementNS(SVGNS,tag);e.setAttribute("class",cls);svg.append(e);return e};
  const track=mk("path","k-track"),val=mk("path","k-val"),cap=mk("circle","k-cap"),ptr=mk("line","k-ptr");
  track.setAttribute("d",arcD(A0,A1));cap.setAttribute("cx",24);cap.setAttribute("cy",24);cap.setAttribute("r",12);
  ptr.setAttribute("x1",24);ptr.setAttribute("y1",21);ptr.setAttribute("x2",24);ptr.setAttribute("y2",13);
  dial.append(svg);
  const lab=document.createElement("span");lab.className="knob-label";lab.textContent=o.label;
  const out=document.createElement("span");out.className="knob-value";
  el.append(dial,lab,out);box.append(el);
  const toV=t=>o.log?o.min*Math.pow(o.max/o.min,t):lerp(o.min,o.max,t);
  const toT=v=>clamp(o.log?Math.log(v/o.min)/Math.log(o.max/o.min):(v-o.min)/(o.max-o.min),0,1);
  let t=0,def=0;
  function render(){const a=lerp(A0,A1,t);
    val.setAttribute("d",t>0.004?arcD(A0,a):"");ptr.setAttribute("transform","rotate("+a.toFixed(1)+" 24 24)");
    const txt=o.fmt(toV(t));out.textContent=txt;dial.setAttribute("aria-valuenow",Math.round(t*100));dial.setAttribute("aria-valuetext",txt)}
  function setT(nt){nt=clamp(nt,0,1);if(nt===t)return;t=nt;render();o.onInput(toV(t))}
  let drag=null;
  dial.addEventListener("pointerdown",e=>{drag={y:e.clientY,t};dial.setPointerCapture(e.pointerId);dial.focus();e.preventDefault()});
  dial.addEventListener("pointermove",e=>{if(drag)setT(drag.t+(drag.y-e.clientY)/(e.shiftKey?600:160))});
  const end=()=>{drag=null};dial.addEventListener("pointerup",end);dial.addEventListener("pointercancel",end);
  dial.addEventListener("dblclick",()=>setT(def));
  dial.addEventListener("wheel",e=>{e.preventDefault();setT(t-Math.sign(e.deltaY)*0.03)},{passive:false});
  dial.addEventListener("keydown",e=>{const st=e.shiftKey?0.1:0.02,m={ArrowUp:st,ArrowRight:st,ArrowDown:-st,ArrowLeft:-st,PageUp:0.1,PageDown:-0.1}[e.key];
    if(m!=null){e.preventDefault();setT(t+m)}else if(e.key==="Home"){e.preventDefault();setT(0)}else if(e.key==="End"){e.preventDefault();setT(1)}});
  render();
  return {set(v,asDefault){t=toT(v);if(asDefault)def=t;render()}};
}
const pct=max=>v=>Math.round(v/max*100)+"%";
const VKNOBS=[
  {key:"rate",label:"Скорость",min:0.25,max:1.5,log:true,fmt:v=>"×"+v.toFixed(2)},
  {key:"cutoff",label:"Яркость",min:200,max:12000,log:true,fmt:v=>v>=1000?(v/1000).toFixed(1)+" кГц":Math.round(v)+" Гц"},
  {key:"fb",label:"Эхо",min:0,max:0.85,fmt:pct(0.85)},
  {key:"wet",label:"Простор",min:0,max:1,fmt:pct(1)},
  {key:"tremDepth",label:"Дрожь",min:0,max:0.9,fmt:pct(0.9)},
  {key:"wob",label:"Плавание",min:0,max:0.05,fmt:pct(0.05)}
];
const voiceKnobs={};
VKNOBS.forEach(k=>{voiceKnobs[k.key]=makeKnob($("voiceKnobs"),Object.assign({},k,{onInput:v=>{if(!current)return;current.V[k.key]=v;if(voice&&AC)tweakVoice(voice,current.V,AC)}}))});
function syncVoiceKnobs(p){VKNOBS.forEach(k=>voiceKnobs[k.key].set(p.V[k.key],true));$("reverse").checked=!!p.V.reverse}
$("reverse").addEventListener("change",e=>{if(!current)return;current.V.reverse=e.target.checked;if(voice){stopVoice();startVoice()}});
$("voiceReset").addEventListener("click",()=>{if(!current)return;current.V=voiceParams(current,current.G);syncVoiceKnobs(current);
  if(voice){stopVoice();startVoice()}setNote("Голос сброшен.")});

let viewPending=false;
const redrawSoon=()=>{if(viewPending)return;viewPending=true;requestAnimationFrame(()=>{viewPending=false;redraw()});setTimeout(()=>{if(viewPending){viewPending=false;redraw()}},120)};
[{key:"rag",label:"Грязь"},{key:"drift",label:"Распад"},{key:"splat",label:"Плотность"},{key:"pix",label:"Пиксель",fmt:v=>(1+Math.round(v*7))+" px"}].forEach(k=>{
  const kn=makeKnob($("viewKnobs"),{label:k.label,min:0,max:1,fmt:k.fmt||pct(1),onInput:v=>{state[k.key]=v;redrawSoon()}});kn.set(state[k.key],true)});

/* ---------- старт ---------- */
(function(){
  const d=demoSound(),A=analyze(d.samples,d.sr);
  const p={id:++uid,sounds:[{samples:d.samples,sr:d.sr,label:"пример",A}],root:A.seed,variant:0,gen:1,A};
  prepare(p);plants.push(p);current=p;show(p,true);
  setNote("Пример. Загрузи свой звук.");
})();
})();
