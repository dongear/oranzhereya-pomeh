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
const easeBack=p=>{const c=1.6;return 1+(c+1)*Math.pow(p-1,3)+c*Math.pow(p-1,2)};
function fmtTime(s){const m=Math.floor(s/60),r=Math.floor(s%60);return m+":"+String(r).padStart(2,"0")}
function plural(n,f){const a=n%10,b=n%100;return f[a===1&&b!==11?0:a>=2&&a<=4&&(b<10||b>=20)?1:2]}
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
  sound:{name:"От звука"},
  greenhouse:{name:"Оранжерея",bg:"#DDE5DA",stem:"#1F3B2C",leaf:"#4E7A55",leaf2:"#8FA97A",flower:"#B8336A",flower2:"#E7A1C0",detail:"#1F3B2C",fa:0.75},
  night:{name:"Ночная теплица",bg:"#1A1424",stem:"#4FD1A5",leaf:"#2E8F73",leaf2:"#8C6BE0",flower:"#E25BB0",flower2:"#F2C6E8",detail:"#F2C6E8",fa:0.7},
  cyan:{name:"Цианотипия",bg:"#1C4E8A",stem:"#F4F7FB",leaf:"#BFD3EA",leaf2:"#8DB0D8",flower:"#FFFFFF",flower2:"#E8F0FA",detail:"#F4F7FB",fa:0.2},
  ink:{name:"Чернила",bg:"#FFFFFF",stem:"#111111",leaf:"#444444",leaf2:"#888888",flower:"#111111",flower2:"#DDDDDD",detail:"#111111",fa:0.12}
};
const hsl=(h,s,l)=>"hsl("+((h%360+360)%360).toFixed(0)+","+s+"%,"+l+"%)";
function colors(key,G){
  let c;
  if(key==="sound"){const h=G.hue,lh=95+G.mid*60;
    c={bg:hsl(h,22,92),stem:hsl(155,32,19),leaf:hsl(lh,32,38),leaf2:hsl(lh+25,30,58),flower:hsl(h,62,52),flower2:hsl(h+35,72,80),detail:hsl(h,30,17),fa:0.78}}
  else c=Object.assign({},PALETTES[key]);
  if(G.muts.has("pale"))c.fa*=0.35;
  return c;
}
function chipsFor(key){
  if(key==="sound")return [hsl(300,22,92),hsl(130,32,38),hsl(300,62,52),hsl(30,62,52)];
  const p=PALETTES[key];return [p.bg,p.leaf,p.flower,p.stem];
}

/* ---------- гены ---------- */
const ARCHE_RU={tree:"ветвистое",weeper:"плакучее",vine:"вьющееся",fern:"папоротник",thistle:"колючее",sundew:"росянка",bulb:"луковичное"};
const MUTS={
  eyes:{ru:"глаза вместо цветов",line:"Иногда смотрит в ответ."},
  threads:{ru:"висящие нити",line:"С веток свисают нити, их лучше не трогать."},
  twin:{ru:"тень-двойник",line:"Рядом всегда стоит его бледная тень."},
  spores:{ru:"споры в воздухе",line:"Пылит спорами, когда слышит своё имя."},
  drips:{ru:"капли с лепестков",line:"По ночам с лепестков капает."},
  pale:{ru:"бледность",line:"Почти не держит цвет."},
  thorns:{ru:"шипы",line:"Шипы выросли сами, никто не просил."},
  spiral:{ru:"закрученные стебли",line:"Стебли закручиваются, когда рядом поют."},
  broken:{ru:"надлом",line:"Стебель надломлен, но растёт дальше."}
};

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
  quiet:{la:["tacitus","tacita","tacitum"],ru:["тихий","тихая"]},
  loud:{la:["clamosus","clamosa","clamosum"],ru:["громкий","громкая"]},
  noisy:{la:["raucus","rauca","raucum"],ru:["шершавый","шершавая"]},
  bright:{la:["lucidus","lucida","lucidum"],ru:["звонкий","звонкая"]},
  dark:{la:["obscurus","obscura","obscurum"],ru:["глухой","глухая"]},
  pulse:{la:["pulsans","pulsans","pulsans"],ru:["дрожащий","дрожащая"]},
  long:{la:["longaevus","longaeva","longaevum"],ru:["долгий","долгая"]},
  short:{la:["brevis","brevis","breve"],ru:["короткий","короткая"]}
};
const RU_NOUN={tree:["Звонник","m"],weeper:["Плакальщица","f"],vine:["Вьюн","m"],fern:["Шелестник","m"],thistle:["Скрипень","m"],sundew:["Росянка","f"],bulb:["Гудень","m"]};

function makeNames(p,G){
  const r=mulberry32(hashInts(p.root,p.variant*17+3));
  const pre=GEN_P[Math.floor(r()*GEN_P.length)],suf=GEN_S[Math.floor(r()*GEN_S.length)];
  const sc=[["quiet",1-G.loud],["loud",G.loud],["noisy",G.noisy*1.2],["bright",G.bright],["dark",1-G.bright],["pulse",G.pulse*0.9],["long",G.longness],["short",1-G.longness]]
    .map(([k,v])=>[k,v+r()*0.35]).sort((a,b)=>b[1]-a[1]);
  const t=TRAITS[sc[0][0]],gi={m:0,f:1,n:2}[suf[1]];
  const genus=pre+suf[0],epi=t.la[gi];
  let latin=genus+" "+epi;
  if(G.muts.has("eyes"))latin+=" var. oculata";else if(G.muts.has("drips"))latin+=" var. lacrimosa";
  const noun=RU_NOUN[G.arche];
  return {latin,ru:noun[0]+" "+t.ru[noun[1]==="f"?1:0],file:(genus+"_"+epi).toLowerCase()};
}

function describe(G){
  const s=[];
  s.push(G.loud>0.5?"Любит громкие комнаты.":"Растёт в тишине и полумраке.");
  s.push(G.noisy>0.45?"Колется, если подойти слишком близко.":"Листья гладкие и прохладные.");
  s.push(G.bright>0.45?"Цветы звенят на сквозняке.":"Цветёт низко и глухо, почти неслышно.");
  const m=[...G.muts];if(m.length)s.push(MUTS[m[0]].line);
  s.push(G.gen>1?"Съело "+G.gen+" "+plural(G.gen,["звук","звука","звуков"])+" и помнит каждый.":"Повторяет услышанное медленнее и тише.");
  return s.join(" ");
}

/* ---------- рисование частей ---------- */
let AM=1; // множитель прозрачности (для тени-двойника)

// gaps: массив флагов по точкам, 1 = разрыв стебля (абстракция)
function drawTaper(ctx,pts,w0,w1,p,col,outline,alpha,gaps){
  const n=pts.length-1,L=p*n,k=Math.floor(L),fr=L-k;
  const sub=pts.slice(0,k+1);
  if(k<n&&fr>0){const a=pts[k],b=pts[k+1];sub.push([lerp(a[0],b[0],fr),lerp(a[1],b[1],fr)])}
  if(sub.length<2)return;
  const m=sub.length,left=[],right=[];
  for(let i=0;i<m;i++){
    const a=sub[Math.max(0,i-1)],b=sub[Math.min(m-1,i+1)];
    let dx=b[0]-a[0],dy=b[1]-a[1];const l=Math.hypot(dx,dy)||1;dx/=l;dy/=l;
    const w=lerp(w0,w1,Math.min(1,i/n))/2;
    left.push([sub[i][0]-dy*w,sub[i][1]+dx*w]);right.push([sub[i][0]+dy*w,sub[i][1]-dx*w]);
  }
  ctx.beginPath();
  let i=0;
  while(i<m){
    while(i<m&&gaps&&gaps[Math.min(i,n)])i++;
    const s=i;while(i<m&&!(gaps&&gaps[Math.min(i,n)]))i++;
    const e=Math.min(m-1,i);if(e-s<1)continue;
    ctx.moveTo(left[s][0],left[s][1]);
    for(let j=s+1;j<=e;j++)ctx.lineTo(left[j][0],left[j][1]);
    for(let j=e;j>=s;j--)ctx.lineTo(right[j][0],right[j][1]);
    ctx.closePath();
  }
  ctx.globalAlpha=(alpha==null?1:alpha)*AM;ctx.fillStyle=col;ctx.fill();
  if(outline){ctx.globalAlpha=0.85*AM;ctx.strokeStyle=outline.col;ctx.lineWidth=outline.w;ctx.stroke()}
}

function strokeLine(ctx,pts,p,col,w,alpha){
  const n=pts.length-1,L=p*n,k=Math.floor(L),fr=L-k;
  ctx.beginPath();ctx.moveTo(pts[0][0],pts[0][1]);
  for(let i=1;i<=k;i++)ctx.lineTo(pts[i][0],pts[i][1]);
  if(k<n&&fr>0){const a=pts[k],b=pts[k+1];ctx.lineTo(lerp(a[0],b[0],fr),lerp(a[1],b[1],fr))}
  ctx.globalAlpha=alpha*AM;ctx.strokeStyle=col;ctx.lineWidth=w;ctx.lineCap="round";ctx.lineJoin="round";ctx.stroke();
}

function leafPath(ctx,shape,L,W){
  ctx.beginPath();
  if(shape==="lance"||shape==="strap"){const w=W*0.5;ctx.moveTo(0,0);ctx.bezierCurveTo(L*0.2,-w,L*0.6,-w,L,0);ctx.bezierCurveTo(L*0.6,w,L*0.2,w,0,0)}
  else if(shape==="heart"){ctx.moveTo(L*0.12,0);ctx.bezierCurveTo(-L*0.08,-W*1.15,L*0.55,-W*1.2,L,0);ctx.bezierCurveTo(L*0.55,W*1.2,-L*0.08,W*1.15,L*0.12,0)}
  else if(shape==="lobed"){
    const top=[],bot=[];
    for(let i=0;i<=24;i++){const t=i/24,w=Math.sin(Math.PI*t)*W*(0.55+0.45*Math.abs(Math.sin(t*Math.PI*4.5)));top.push([t*L,-w]);bot.push([t*L,w])}
    ctx.moveTo(0,0);top.forEach(q=>ctx.lineTo(q[0],q[1]));for(let i=bot.length-1;i>=0;i--)ctx.lineTo(bot[i][0],bot[i][1]);
  }
  else if(shape==="round"){ctx.moveTo(L*0.95,0);ctx.arc(L*0.62,0,L*0.33,0,TAU)}
  else{ctx.moveTo(0,0);ctx.bezierCurveTo(L*0.25,-W,L*0.75,-W,L,0);ctx.bezierCurveTo(L*0.75,W,L*0.25,W,0,0)}
  ctx.closePath();
}

// абстрактные листья: заливка сдвинута (как в ризографии), контур на месте
function absLeafPath(ctx,l){
  const L=l.L,W=l.W;ctx.beginPath();
  switch(l.kind){
    case "dot":ctx.arc(L*0.55,0,L*0.3,0,TAU);break;
    case "ring":ctx.arc(L*0.55,0,L*0.32,0,TAU);ctx.moveTo(L*0.55+L*0.14,0);ctx.arc(L*0.55,0,L*0.14,0,TAU);break;
    case "bar":ctx.rect(0,-W*0.22,L,W*0.44);break;
    case "tri":ctx.moveTo(0,-W*0.7);ctx.lineTo(L,0);ctx.lineTo(0,W*0.7);ctx.closePath();break;
    case "arc":ctx.arc(L*0.15,0,L*0.6,-1.1,1.1);break;
    case "dots":for(let k=0;k<4;k++){const x=L*(0.2+k*0.25),r=W*(0.42-k*0.07);ctx.moveTo(x+r,0);ctx.arc(x,0,r,0,TAU)}break;
    default:ctx.arc(L*0.5,0,L*0.4,Math.PI,0);ctx.closePath();
  }
}
function drawAbsLeaf(ctx,l,s,C){
  ctx.save();ctx.translate(l.x+C.sx,l.y+C.sy);ctx.rotate(l.a);ctx.scale(s,s);
  absLeafPath(ctx,l);
  if(l.kind==="arc"){ctx.globalAlpha=0.8*AM;ctx.strokeStyle=l.col;ctx.lineWidth=l.W*0.35;ctx.lineCap="round";ctx.stroke()}
  else{ctx.globalAlpha=Math.max(C.fa,0.3)*AM;ctx.fillStyle=l.col;ctx.fill("evenodd")}
  ctx.restore();
  if(l.kind==="arc"||l.kind==="dots")return;
  ctx.save();ctx.translate(l.x,l.y);ctx.rotate(l.a);ctx.scale(s,s);
  absLeafPath(ctx,l);ctx.globalAlpha=0.8*AM;ctx.strokeStyle=C.stem;ctx.lineWidth=C.u*1.2;ctx.stroke();
  ctx.restore();
}

function drawLeaf(ctx,l,p,C){
  const s=easeOut(p);if(s<=0.01)return;
  if(l.kind){drawAbsLeaf(ctx,l,s,C);return}
  if(l.shape!=="needle"&&(C.sx||C.sy)){
    ctx.save();ctx.translate(l.x+C.sx,l.y+C.sy);ctx.rotate(l.a);ctx.scale(s,s);
    leafPath(ctx,l.shape,l.L,l.W);ctx.globalAlpha=C.fa*AM;ctx.fillStyle=l.col;ctx.fill();ctx.restore();
  }
  ctx.save();ctx.translate(l.x,l.y);ctx.rotate(l.a);ctx.scale(s,s);
  ctx.strokeStyle=C.stem;ctx.lineCap="round";
  if(l.shape==="needle"){
    ctx.lineWidth=C.u*1.6;ctx.globalAlpha=0.9*AM;ctx.beginPath();
    for(let k=-1;k<=1;k++){ctx.moveTo(0,0);ctx.lineTo(l.L*Math.cos(k*0.35)*(k?0.75:1),l.L*Math.sin(k*0.35)*0.75)}
    ctx.stroke();ctx.restore();return;
  }
  if(l.shape==="round"){ctx.lineWidth=C.u*1.3;ctx.globalAlpha=0.85*AM;ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(l.L*0.3,0);ctx.stroke()}
  leafPath(ctx,l.shape,l.L,l.W);
  if(!(C.sx||C.sy)){ctx.globalAlpha=C.fa*AM;ctx.fillStyle=l.col;ctx.fill()}
  ctx.globalAlpha=0.85*AM;ctx.lineWidth=C.u*1.3;ctx.stroke();
  if(l.shape!=="round"){ctx.globalAlpha=0.45*AM;ctx.lineWidth=C.u;ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(l.L*0.82,0);ctx.stroke()}
  ctx.restore();
}

function drawAbsFlower(ctx,f,s,C){
  const r=f.r*1.1,u=C.u;
  ctx.save();ctx.translate(f.x+C.sx,f.y+C.sy);ctx.scale(s,s);
  ctx.globalAlpha=Math.max(C.fa,0.35)*AM;ctx.fillStyle=f.col;
  if(f.kind==="halo"||f.kind==="rings"){ctx.beginPath();ctx.arc(0,0,r*(f.kind==="halo"?0.75:0.45),0,TAU);ctx.fill()}
  else if(f.kind==="disc"){ctx.rotate(f.a);ctx.beginPath();ctx.arc(0,0,r*0.85,-Math.PI/2,Math.PI/2);ctx.closePath();ctx.fill()}
  else if(f.kind==="grid"){for(let a=-1;a<=1;a++)for(let b=-1;b<=1;b++){ctx.beginPath();ctx.arc(a*r*0.42,b*r*0.42,r*(0.1+f.rays[(a+1)*3+b+1]*0.12),0,TAU);ctx.fill()}}
  ctx.restore();
  ctx.save();ctx.translate(f.x,f.y);ctx.scale(s,s);
  ctx.strokeStyle=C.stem;ctx.lineWidth=u*1.3;ctx.lineCap="round";ctx.globalAlpha=0.85*AM;
  switch(f.kind){
    case "rings":for(let k=1;k<=3;k++){ctx.beginPath();ctx.arc(0,0,r*k/3,0,TAU);ctx.stroke()}break;
    case "halo":ctx.beginPath();ctx.arc(0,0,r,0,TAU);ctx.stroke();break;
    case "burst":ctx.beginPath();for(let k=0;k<f.n+4;k++){const a=f.rot+k/(f.n+4)*TAU,rr=r*f.rays[k%30];ctx.moveTo(Math.cos(a)*r*0.2,Math.sin(a)*r*0.2);ctx.lineTo(Math.cos(a)*rr,Math.sin(a)*rr)}ctx.stroke();
      ctx.fillStyle=f.col;for(let k=0;k<f.n+4;k+=2){const a=f.rot+k/(f.n+4)*TAU,rr=r*f.rays[k%30];ctx.beginPath();ctx.arc(Math.cos(a)*rr,Math.sin(a)*rr,r*0.07,0,TAU);ctx.fill()}break;
    case "disc":ctx.rotate(f.a);ctx.beginPath();ctx.moveTo(0,-r*0.85);ctx.lineTo(0,r*0.85);ctx.stroke();ctx.beginPath();ctx.arc(0,0,r*0.85,-Math.PI/2,Math.PI/2);ctx.stroke();break;
    case "grid":ctx.beginPath();ctx.rect(-r*0.7,-r*0.7,r*1.4,r*1.4);ctx.stroke();break;
  }
  ctx.globalAlpha=AM;ctx.fillStyle=C.detail;ctx.beginPath();ctx.arc(0,0,r*0.1,0,TAU);ctx.fill();
  ctx.restore();
}

function drawFlower(ctx,f,p,C){
  const s=easeBack(p);if(s<=0.01)return;
  if(f.kind){drawAbsFlower(ctx,f,s,C);return}
  const r=f.r,u=C.u;
  if(C.sx||C.sy){ctx.save();ctx.globalAlpha=0.35*AM;ctx.fillStyle=f.col2;ctx.beginPath();ctx.arc(f.x+C.sx*1.4,f.y+C.sy*1.4,r*0.7*s,0,TAU);ctx.fill();ctx.restore()}
  ctx.save();ctx.translate(f.x,f.y);
  ctx.lineWidth=u*1.3;ctx.strokeStyle=C.stem;ctx.lineCap="round";ctx.lineJoin="round";
  if(f.glow){const g=ctx.createRadialGradient(0,0,0,0,0,r*2.6*s);g.addColorStop(0,f.col2);g.addColorStop(1,"rgba(0,0,0,0)");
    ctx.globalAlpha=0.45*AM;ctx.fillStyle=g;ctx.beginPath();ctx.arc(0,0,r*2.6*s,0,TAU);ctx.fill()}
  if(f.type==="bell"||f.type==="eye"){ctx.scale(s,s)}else{ctx.rotate(f.a);ctx.scale(s,s)}
  const fillA=Math.max(C.fa,0.25)*AM;
  switch(f.type){
    case "daisy":{
      for(let k=0;k<f.n;k++){const a=f.rot+k/f.n*TAU;ctx.beginPath();ctx.ellipse(Math.cos(a)*r*0.55,Math.sin(a)*r*0.55,r*0.5,r*0.16,a,0,TAU);
        ctx.globalAlpha=fillA;ctx.fillStyle=f.col;ctx.fill();ctx.globalAlpha=0.8*AM;ctx.stroke()}
      ctx.beginPath();ctx.arc(0,0,r*0.22,0,TAU);ctx.globalAlpha=AM;ctx.fillStyle=C.detail;ctx.fill();break}
    case "star":{
      const n=Math.max(5,f.n>>1);ctx.beginPath();
      for(let k=0;k<n*2;k++){const a=f.rot+k/(n*2)*TAU,rr=k%2?r*0.3:r;ctx[k?"lineTo":"moveTo"](Math.cos(a)*rr,Math.sin(a)*rr)}
      ctx.closePath();ctx.globalAlpha=fillA;ctx.fillStyle=f.col;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.stroke();
      ctx.beginPath();ctx.arc(0,0,r*0.12,0,TAU);ctx.globalAlpha=AM;ctx.fillStyle=C.detail;ctx.fill();break}
    case "tulip":{
      [[-0.4,f.col2],[0.4,f.col2],[0,f.col]].forEach(([a,c])=>{ctx.beginPath();ctx.ellipse(Math.cos(a)*r*0.5,Math.sin(a)*r*0.5,r*0.58,r*0.28,a,0,TAU);
        ctx.globalAlpha=Math.max(fillA,0.6*AM);ctx.fillStyle=c;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.stroke()});break}
    case "bell":{
      ctx.beginPath();ctx.moveTo(0,0);ctx.quadraticCurveTo(r*0.25,r*0.15,0,r*0.45);ctx.globalAlpha=0.85*AM;ctx.stroke();
      const t=r*0.45;ctx.beginPath();ctx.moveTo(-r*0.18,t);
      ctx.bezierCurveTo(-r*0.45,t+r*0.3,-r*0.4,t+r*0.8,-r*0.7,t+r*1.05);
      ctx.quadraticCurveTo(-r*0.2,t+r*0.85,0,t+r*1.0);ctx.quadraticCurveTo(r*0.2,t+r*0.85,r*0.7,t+r*1.05);
      ctx.bezierCurveTo(r*0.4,t+r*0.8,r*0.45,t+r*0.3,r*0.18,t);ctx.closePath();
      ctx.globalAlpha=fillA;ctx.fillStyle=f.col;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.stroke();
      ctx.beginPath();ctx.moveTo(0,t+r*0.6);ctx.lineTo(f.rot>3?r*0.08:-r*0.08,t+r*1.35);ctx.stroke();
      ctx.beginPath();ctx.arc(f.rot>3?r*0.08:-r*0.08,t+r*1.35,r*0.08,0,TAU);ctx.globalAlpha=AM;ctx.fillStyle=C.detail;ctx.fill();break}
    case "orb":{
      ctx.beginPath();ctx.moveTo(0,-r*0.1);ctx.lineTo(r*0.5,-r*0.38);ctx.lineTo(r*0.45,r*0.38);ctx.lineTo(0,r*0.1);ctx.closePath();
      ctx.globalAlpha=Math.max(C.fa,0.3)*AM;ctx.fillStyle=C.leaf;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.stroke();
      ctx.save();ctx.translate(r*0.75,0);ctx.strokeStyle=f.col;ctx.lineWidth=u*1.4;ctx.globalAlpha=0.9*AM;ctx.beginPath();
      for(let k=0;k<f.rays.length;k++){const a=f.rot+k/f.rays.length*TAU;ctx.moveTo(Math.cos(a)*r*0.25,Math.sin(a)*r*0.25);ctx.lineTo(Math.cos(a)*r*0.8*f.rays[k],Math.sin(a)*r*0.8*f.rays[k])}
      ctx.stroke();ctx.beginPath();ctx.arc(0,0,r*0.3,0,TAU);ctx.globalAlpha=Math.max(fillA,0.6*AM);ctx.fillStyle=f.col2;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.strokeStyle=C.stem;ctx.stroke();ctx.restore();break}
    case "spore":{
      ctx.save();ctx.translate(r*0.2,0);ctx.lineWidth=u;ctx.globalAlpha=0.8*AM;ctx.strokeStyle=C.stem;
      for(let k=0;k<22;k++){const a=f.rot+k/22*TAU,rr=r*0.95*f.rays[k];ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(Math.cos(a)*rr,Math.sin(a)*rr);ctx.stroke();
        ctx.beginPath();ctx.arc(Math.cos(a)*rr,Math.sin(a)*rr,r*0.07,0,TAU);ctx.fillStyle=f.col;ctx.fill()}
      ctx.beginPath();ctx.arc(0,0,r*0.12,0,TAU);ctx.fillStyle=C.detail;ctx.globalAlpha=AM;ctx.fill();ctx.restore();break}
    case "bud":{
      ctx.beginPath();ctx.moveTo(0,0);ctx.bezierCurveTo(r*0.2,-r*0.5,r*0.9,-r*0.32,r*1.15,0);ctx.bezierCurveTo(r*0.9,r*0.32,r*0.2,r*0.5,0,0);
      ctx.globalAlpha=Math.max(fillA,0.6*AM);ctx.fillStyle=f.col;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.stroke();
      ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(r*0.45,-r*0.28);ctx.moveTo(0,0);ctx.lineTo(r*0.45,r*0.28);ctx.stroke();break}
    case "eye":{
      const R=r*1.1;
      ctx.beginPath();ctx.moveTo(-R,0);ctx.quadraticCurveTo(0,-R*0.95,R,0);ctx.quadraticCurveTo(0,R*0.95,-R,0);ctx.closePath();
      ctx.globalAlpha=0.95*AM;ctx.fillStyle=f.col2;ctx.fill();ctx.strokeStyle=C.detail;ctx.stroke();
      const lx=Math.cos(f.rot)*R*0.18,ly=Math.sin(f.rot)*R*0.1;
      ctx.beginPath();ctx.arc(lx,ly,R*0.36,0,TAU);ctx.fillStyle=f.col;ctx.fill();
      ctx.beginPath();ctx.arc(lx,ly,R*0.15,0,TAU);ctx.fillStyle=C.detail;ctx.fill();
      ctx.beginPath();for(let k=0;k<6;k++){const t=-0.7+k*0.28,x=Math.sin(t)*R*0.85,y=-Math.cos(t)*R*0.45-R*0.02;ctx.moveTo(x,y);ctx.lineTo(x*1.12,y-R*0.22)}ctx.stroke();break}
  }
  ctx.restore();
}

/* ---------- рост ---------- */
const LEAF_KINDS=["dot","ring","bar","tri","arc","dots","half"];
const FLOWER_KINDS=["rings","halo","burst","disc","grid"];
// X: {a: абстракция, drift: распад, shift: сдвиг цвета}, все 0..1
function buildPlant(plant,G,C,W,H,cap,X){
  const u=Math.min(W,H)/1000,wide=W>H,rng=mulberry32(G.geo),F=plant.A.frames;
  // отдельный генератор для абстракции: ручки не перетасовывают само растение
  const ar=mulberry32(G.geo^0x5bd1e995);
  const fr=x=>F[clamp(Math.floor(x*F.length),0,F.length-1)];
  C.u=u;
  const sa=ar()*TAU;C.sx=Math.cos(sa)*X.shift*14*u;C.sy=Math.sin(sa)*X.shift*14*u;
  const textSide=wide&&cap;
  const bx=textSide?W*0.32:W/2;
  const gy=H*(cap&&!wide?0.79:0.85);
  const top=H*0.06,Hh=gy-top,PH=G.height*Hh;
  const spread=Math.min(textSide?W*0.29:W*0.45,Hh*0.85);
  const xmin=bx-spread,xmax=bx+spread;
  const rootBottom=cap&&!wide?gy+(H-gy)*0.48:H*0.975;
  const ops=[],anchors=[],flowers=[];
  const bbox={x0:bx,x1:bx,y0:gy,y1:gy};
  let stemCount=0,kinked=false,rootCount=0;
  const add=(L,t0,t1,f)=>{t0=clamp(t0,0,0.97);ops.push({L,t0,t1:clamp(Math.max(t1,t0+0.02),0,1),f})};

  function path(x,y,ang,len,n,o){
    const pts=[[x,y]],angs=[ang],sl=len/n;let cs=1;
    for(let i=1;i<=n;i++){
      const q=i/n,f=fr((o.fOff||0)+(o.fSpan||0)*q);
      ang+=(o.curl||0)*cs+(rng()-.5)*o.wobble*0.25+(f.bands[(i*3)%NB]-0.45)*0.1*o.wobble;
      if(o.alt&&f.onset)cs=-cs;
      if(o.curlRamp)ang+=o.curlRamp*Math.pow(q,4);
      if(o.up)ang+=angDiff(-Math.PI/2,ang)*o.up;
      if(o.droop)ang+=angDiff(Math.PI/2,ang)*o.droop*q;
      if(o.kink&&i===Math.round(n*0.45))ang+=o.kink;
      ang+=(ar()-.5)*X.a*0.3;
      if(X.a>0.3){const g=Math.PI/6;ang+=angDiff(Math.round(ang/g)*g,ang)*(X.a-0.3)*0.3}
      const nx=x+Math.cos(ang)*sl,ny=y+Math.sin(ang)*sl;
      let st=0;
      if(o.root){
        if(ny<gy+6*u)st=angDiff(Math.PI/2,ang);
        else if(ny>rootBottom)st=angDiff(nx<bx?Math.PI:0,ang);
        if(nx<xmin||nx>xmax)st=angDiff(Math.PI/2,ang);
      }else{
        if(nx<xmin)st=angDiff(-Math.PI/4,ang);
        else if(nx>xmax)st=angDiff(-Math.PI*3/4,ang);
        if(ny<top)st=angDiff(nx<bx?0:Math.PI,ang)*0.6+angDiff(Math.PI/2,ang)*0.4;
        if(ny>gy-4*u&&!o.free)st=angDiff(-Math.PI/2,ang);
      }
      ang+=st*0.35;
      x+=Math.cos(ang)*sl;y+=Math.sin(ang)*sl;
      pts.push([x,y]);angs.push(ang);
    }
    return {pts,angs};
  }
  function track(pts){pts.forEach(q=>{bbox.x0=Math.min(bbox.x0,q[0]);bbox.x1=Math.max(bbox.x1,q[0]);bbox.y0=Math.min(bbox.y0,q[1]);bbox.y1=Math.max(bbox.y1,q[1])})}
  function stem(P,w0,w1,t0,t1,col,lay,outline){
    track(P.pts);
    const n=P.pts.length,gaps=new Uint8Array(n),sk=[];let gap=0;
    for(let i=0;i<n;i++){
      const r1=ar(),r2=ar(),r3=ar();
      if(gap>0){gaps[i]=1;gap--}else if(i>3&&i<n-3&&r1<X.a*0.08)gap=1+Math.floor(r2*3);
      const a=P.angs[i]+Math.PI/2,o=(w0*0.6+(3+r3*5)*u)*(1-i/n*0.5);
      sk.push([P.pts[i][0]+Math.cos(a)*o,P.pts[i][1]+Math.sin(a)*o]);
    }
    const useGaps=X.a>0.05?gaps:null;
    add(lay||2,t0,t1,(ctx,q)=>{drawTaper(ctx,P.pts,w0,w1,q,col||C.stem,outline,1,useGaps);
      if(X.a>0.15)strokeLine(ctx,sk,q,col||C.stem,0.9*u,0.55*X.a)});
    for(let i=4;i<P.pts.length;i+=6)anchors.push({x:P.pts[i][0],y:P.pts[i][1],t:lerp(t0,t1,i/(P.pts.length-1))});
  }
  function leaf(x,y,a,L,t,shape){
    const l={x,y,a,L,W:L*0.38,shape:shape||G.leafShape,col:rng()<0.55?C.leaf:C.leaf2};
    const r1=ar(),r2=ar(),r3=ar(),r4=ar(),r5=ar();
    if(r1<X.a*0.8)l.kind=LEAF_KINDS[Math.floor(r2*LEAF_KINDS.length)];
    if(r3<X.drift*0.7){const d=(15+r4*150)*u*X.drift;l.x+=Math.cos(a)*d;l.y+=Math.sin(a)*d;l.a+=(r5-.5)*2.5*X.drift}
    add(3,t,t+0.07,(ctx,q)=>drawLeaf(ctx,l,q,C));
  }
  function flower(x,y,a,r,t,type){
    type=type||G.flowerType;
    if(G.muts.has("eyes")&&rng()<0.4)type="eye";
    const f={x,y,a,r,type,n:6+Math.floor(rng()*9),rot:rng()*TAU,rays:Array.from({length:30},()=>0.55+rng()*0.45),
      col:rng()<0.8?C.flower:C.flower2,col2:C.flower2,glow:G.arche==="bulb"};
    if(type==="eye")f.col=C.flower;
    const r1=ar(),r2=ar(),r3=ar(),r4=ar();
    if(type!=="eye"&&r1<X.a*0.75)f.kind=FLOWER_KINDS[Math.floor(r2*FLOWER_KINDS.length)];
    if(r3<X.drift*0.5){const d=(10+r4*90)*u*X.drift;f.x+=Math.cos(a)*d;f.y+=Math.sin(a)*d}
    const t0=Math.min(t,0.86);
    add(4,t0,t0+0.12,(ctx,q)=>drawFlower(ctx,f,q,C));
    flowers.push({x,y,r,t:t0,type,col:f.col});
    track([[x-r,y-r],[x+r,y+r]]);
  }
  function pedicel(x0,y0,x1,y1,t){const pts=[[x0,y0],[x1,y1]];add(2,t,t+0.03,(ctx,q)=>strokeLine(ctx,pts,q,C.stem,1.6*u,0.9))}
  function thorns(P,w0,w1,t0,t1){
    const list=[];let side=1;
    for(let i=2;i<P.pts.length-1;i+=3){side=-side;const q=i/(P.pts.length-1),a=P.angs[i];
      list.push({x:P.pts[i][0],y:P.pts[i][1],a,side,w:lerp(w0,w1,q)/2,len:(5+rng()*8)*u,q})}
    add(2,t0,t1,(ctx,p)=>{ctx.globalAlpha=AM;ctx.fillStyle=C.stem;ctx.beginPath();
      list.forEach(t=>{if(t.q>p)return;const nx=Math.cos(t.a+t.side*Math.PI/2),ny=Math.sin(t.a+t.side*Math.PI/2),dx=Math.cos(t.a),dy=Math.sin(t.a);
        const bx0=t.x+nx*t.w*0.8,by0=t.y+ny*t.w*0.8,b=Math.max(2*u,t.len*0.35);
        ctx.moveTo(bx0-dx*b,by0-dy*b);ctx.lineTo(bx0+nx*t.len+dx*t.len*0.6,by0+ny*t.len+dy*t.len*0.6);ctx.lineTo(bx0+dx*b,by0+dy*b)});
      ctx.fill()});
  }
  function tendril(x,y,a,side,t){
    const pts=[[x,y]];let ang=a,len=(3.2+rng()*1.5)*u;
    for(let k=0;k<36;k++){ang+=side*(0.08+k*0.012);len*=0.965;x+=Math.cos(ang)*len*2;y+=Math.sin(ang)*len*2;pts.push([x,y])}
    add(2,t,t+0.1,(ctx,q)=>strokeLine(ctx,pts,q,C.stem,1.3*u,0.85));
  }
  const fsize=(f,k)=>(13+f.rms*16)*u*G.flowerSize*(k||1);

  // универсальная ветка
  function grow(x,y,ang,len,w,lvl,t0,t1,fOff,fSpan,o){
    stemCount++;
    const n=Math.max(5,Math.round(len/(8*u)));
    let kink=0;if(lvl===0&&G.muts.has("broken")&&!kinked){kinked=true;kink=(rng()<.5?-1:1)*(0.5+rng()*0.4)}
    const P=path(x,y,ang,len,n,{curl:G.curl*(o.curlK||1)*(rng()<.5?-1:1),wobble:G.wobble*(o.wobK||1),up:o.up[Math.min(lvl,o.up.length-1)],
      droop:o.droop[Math.min(lvl,o.droop.length-1)],alt:o.alt,fOff,fSpan,kink,curlRamp:o.curlRamp?o.curlRamp*(rng()<.5?-1:1):0});
    const w1=w*o.taper;
    stem(P,w,w1,t0,t1);
    if(G.thorns)thorns(P,w,w1,t0,t1);
    const dt=t1-t0;
    if(o.leaves){
      const every=Math.max(2,Math.round(lerp(7,2.5,G.leafDensity)));let side=rng()<.5?1:-1;
      for(let i=2;i<n;i+=every){if(rng()<0.15)continue;const q=i/n,f=fr(fOff+fSpan*q);side=-side;
        const L=o.leafL*u*G.leafSize*(0.55+f.rms*0.8)*(1-q*0.35)*Math.pow(0.82,lvl);
        leaf(P.pts[i][0],P.pts[i][1],P.angs[i]+side*(0.6+rng()*0.5),L,t0+dt*q);
        if(o.pair)leaf(P.pts[i][0],P.pts[i][1],P.angs[i]-side*(0.6+rng()*0.5),L*0.9,t0+dt*q)}
    }
    if(o.side>0)for(let i=3;i<n-2;i++){const q=i/n,f=fr(fOff+fSpan*q);
      if(f.onset&&rng()<o.side){const sa=P.angs[i]+(rng()<.5?-1:1)*(0.7+rng()*0.5),pl=(12+rng()*26)*u;
        const ex=P.pts[i][0]+Math.cos(sa)*pl,ey=P.pts[i][1]+Math.sin(sa)*pl;
        pedicel(P.pts[i][0],P.pts[i][1],ex,ey,t0+dt*q);flower(ex,ey,sa,fsize(f,0.7*(o.flowerK||1)),t0+dt*q+0.03)}}
    if(o.tendrils)for(let i=6;i<n-3;i+=10+Math.floor(rng()*6)){const q=i/n,side=rng()<.5?-1:1;tendril(P.pts[i][0],P.pts[i][1],P.angs[i]+side*0.9,side,t0+dt*q)}
    const kids=lvl<o.maxLvl&&stemCount<o.maxStems?o.kids(lvl):0;
    for(let k=0;k<kids;k++){
      const q=lerp(o.kidFrom,0.94,(k+0.3+rng()*0.5)/kids),i=Math.min(n,Math.round(q*n)),side=(k%2?1:-1)*(rng()<0.2?-1:1);
      const ca=P.angs[i]+side*G.branchAngle*(o.angK||1)*(0.7+rng()*0.6);
      const cl=len*o.lenK*(0.75+rng()*0.4)*(1-q*0.3);
      const ct0=t0+dt*q,ct1=Math.min(0.9,ct0+dt*0.85);
      grow(P.pts[i][0],P.pts[i][1],ca,cl,lerp(w,w1,q)*0.8,lvl+1,ct0,ct1,fOff+fSpan*q,fSpan*(1-q),o);
    }
    const tf=fr(fOff+fSpan);
    if(rng()<(kids?o.tipMid:o.tip))flower(P.pts[n][0],P.pts[n][1],P.angs[n],fsize(tf,o.flowerK),t1);
    else if(o.leaves&&rng()<0.5)leaf(P.pts[n][0],P.pts[n][1],P.angs[n],o.leafL*u*G.leafSize*0.55,t1);
    return P;
  }

  function roots(x,y,count,maxLen,w0){
    for(let k=0;k<count;k++){
      const a=Math.PI/2+(count>1?(k/(count-1)-0.5):0)*2.4+(rng()-.5)*0.35,f=fr(k/count);
      const len=maxLen*(0.35+rng()*0.5)*(0.6+gE(f,0,5)*0.6);
      const n=Math.max(5,Math.round(len/(7*u)));
      const P=path(x+(rng()-.5)*8*u,y,a,len,n,{root:true,wobble:1+G.noisy,curl:(rng()-.5)*0.03});
      rootCount++;
      const t0=0.02+rng()*0.05,t1=0.25+rng()*0.12,ww=w0*(0.6+rng()*0.5);
      add(0,t0,t1,(ctx,q)=>{ctx.save();ctx.beginPath();ctx.rect(0,gy,W,H-gy);ctx.clip();drawTaper(ctx,P.pts,ww,0.6*u,q,C.detail,null,0.55);ctx.restore()});
      for(let j=0;j<2+Math.floor(rng()*2);j++){
        const q=0.25+rng()*0.6,i=Math.round(q*n),side=rng()<.5?-1:1;
        const P2=path(P.pts[i][0],P.pts[i][1],P.angs[i]+side*(0.5+rng()*0.5),len*0.3*(1-q*0.5),Math.max(4,Math.round(n*0.3)),{root:true,wobble:1.4+G.noisy});
        const s0=lerp(t0,t1,q);
        add(0,s0,s0+0.1,(ctx,qq)=>{ctx.save();ctx.beginPath();ctx.rect(0,gy,W,H-gy);ctx.clip();drawTaper(ctx,P2.pts,ww*0.4,0.4*u,qq,C.detail,null,0.45);ctx.restore()});
      }
    }
  }

  // земля
  (function(){
    const gw=Math.min(spread*1.05,W*0.42),pts=[],specks=[];
    for(let i=0;i<=60;i++){const t=i/60;pts.push([bx-gw+t*gw*2,gy+Math.sin(t*9+rng())*1.6*u+(rng()-.5)*1.5*u])}
    for(let i=0;i<70;i++){const t=rng();specks.push([bx-gw*0.9+t*gw*1.8,gy+(3+Math.pow(rng(),2)*30)*u,(0.8+rng()*1.8)*u,Math.abs(t-0.5)])}
    const mid=30,L=pts.slice(0,mid+1).reverse(),R=pts.slice(mid);
    add(1,0,0.14,(ctx,q)=>{strokeLine(ctx,L,q,C.detail,2.2*u,0.8);strokeLine(ctx,R,q,C.detail,2.2*u,0.8);
      ctx.globalAlpha=0.45*AM;ctx.fillStyle=C.detail;specks.forEach(s=>{if(s[3]*2>q)return;ctx.beginPath();ctx.arc(s[0],s[1],s[2],0,TAU);ctx.fill()})});
  })();

  const baseRoots=3+Math.round(G.low*6);
  const rootLen=(rootBottom-gy)*1.1;
  const A=G.arche;
  const wMain=(9+G.loud*13)*u;
  const common={up:[0.05],droop:[0],curlK:1,wobK:1,taper:0.3,leaves:true,leafL:58,side:0.22,kids:()=>2,maxLvl:G.depth,maxStems:150,kidFrom:0.3,angK:1,lenK:0.6,tip:0.75,tipMid:0.12,flowerK:1};

  if(A==="tree"){
    roots(bx,gy,baseRoots,rootLen,wMain*0.6);
    const o=Object.assign({},common,{up:[0.045,0.03,0.02],kids:l=>l===0?3+Math.round(G.mid*2):(rng()<0.45?2:1)+(l<2?1:0),maxLvl:G.stems>1?Math.min(3,G.depth):G.depth});
    for(let s=0;s<G.stems;s++){
      o.maxStems=stemCount+Math.round(150/G.stems);
      const a=-Math.PI/2+(s-(G.stems-1)/2)*0.35+(rng()-.5)*0.2;
      grow(bx+(s-(G.stems-1)/2)*wMain*0.6,gy,a,PH*0.68*(0.85+rng()*0.2),wMain*(s?0.8:1),0,0.08+s*0.05,0.55,0,1,o);
    }
  }else if(A==="weeper"){
    roots(bx,gy,baseRoots,rootLen,wMain*0.5);
    const o=Object.assign({},common,{up:[0.07,0,0],droop:[0,0.1,0.13],angK:1.7,lenK:0.8,kids:l=>l===0?4+Math.round(G.mid*3):2,maxLvl:2,tip:0.85,taper:0.35,side:0.15,leafL:50});
    grow(bx,gy,-Math.PI/2+(rng()-.5)*0.15,PH*0.82,wMain*0.85,0,0.06,0.5,0,1,o);
  }else if(A==="vine"){
    roots(bx,gy,baseRoots,rootLen,wMain*0.4);
    const o=Object.assign({},common,{up:[0.035,0.02],curlK:Math.min(4,0.08/G.curl),wobK:1.3,alt:true,kids:()=>2+Math.round(G.longness*3),maxLvl:1,lenK:0.35,side:0.6,leafL:66,tendrils:true,tip:0.9});
    const vs=G.stems>2?2:1;
    for(let s=0;s<vs;s++)grow(bx+(s?wMain:0),gy,-Math.PI/2+(s?0.3:-0.1),PH*1.4,wMain*0.55,0,0.06+s*0.08,0.7,0,1,o);
  }else if(A==="fern"){
    roots(bx,gy,baseRoots+2,rootLen*0.8,wMain*0.4);
    const nF=5+Math.round(G.mid*4)+Math.min(G.gen-1,3);
    for(let k=0;k<nF;k++){
      const off=nF>1?(k/(nF-1)-0.5)*2:0,ang=-Math.PI/2+off*1.05+(rng()-.5)*0.15;
      const len=PH*(0.95-Math.abs(off)*0.35)*(0.8+rng()*0.25),n=Math.max(8,Math.round(len/(8*u)));
      const P=path(bx+off*10*u,gy,ang,len,n,{wobble:G.wobble*0.6,up:0.015*(1-Math.abs(off)),droop:Math.abs(off)*0.035,curlRamp:(off<0?-1:1)*0.32*(0.8+rng()*0.4),curl:G.curl*0.3,fOff:0,fSpan:1});
      const t0=0.06+rng()*0.12,t1=t0+0.5;
      stem(P,(4.5+G.loud*4)*u,1*u,t0,t1);
      if(G.thorns)thorns(P,(4.5+G.loud*4)*u,1*u,t0,t1);
      const sori=[];
      for(let i=2;i<n-3;i+=3){const q=i/n,f=fr(q),L=58*u*G.leafSize*Math.pow(Math.sin(Math.PI*Math.min(1,q*1.15)),0.7)*(0.6+f.rms*0.6)*0.85;
        if(L<4*u)continue;
        for(const side of[-1,1]){leaf(P.pts[i][0],P.pts[i][1],P.angs[i]+side*(1.0+rng()*0.2),L,lerp(t0,t1,q));
          if(f.onset||rng()<G.pulse*0.2){const a=P.angs[i]+side*1.05;sori.push([P.pts[i][0]+Math.cos(a)*L*0.55,P.pts[i][1]+Math.sin(a)*L*0.55,lerp(t0,t1,q)])}}}
      if(sori.length)add(4,t1-0.05,t1+0.1,(ctx,q)=>{ctx.globalAlpha=0.9*AM;ctx.fillStyle=C.flower;sori.forEach(s=>{ctx.beginPath();ctx.arc(s[0],s[1],3.2*u*q,0,TAU);ctx.fill()})});
      if(G.muts.has("eyes")&&rng()<0.45)flower(P.pts[n][0],P.pts[n][1],0,fsize(fr(1),0.8),t1,"eye");
    }
  }else if(A==="thistle"){
    roots(bx,gy,baseRoots,rootLen,wMain*0.6);
    for(let k=0;k<4+Math.floor(rng()*3);k++){const a=-Math.PI+0.25+rng()*(Math.PI-0.5);leaf(bx+(rng()-.5)*20*u,gy-2*u,a,58*u*2.1*G.leafSize*(0.8+rng()*0.3),0.05+rng()*0.1,"lobed")}
    const nS=2+Math.floor(rng()*2)+(G.gen>2?1:0);
    const o=Object.assign({},common,{up:[0.08,0.06],curlK:0.3,wobK:0.4,taper:0.55,kids:l=>l===0?1+Math.round(rng()*2):1,maxLvl:Math.min(G.depth-1,2),angK:0.7,lenK:0.5,leafL:52,tip:1,tipMid:1,flowerK:1.5,side:0.1});
    for(let s=0;s<nS;s++){const off=nS>1?(s/(nS-1)-0.5)*2:0;
      grow(bx+off*24*u,gy,-Math.PI/2+off*0.55+(rng()-.5)*0.1,PH*(0.6+rng()*0.25),wMain*0.75,0,0.08+s*0.04,0.5+rng()*0.1,0,1,o)}
  }else if(A==="sundew"){
    roots(bx,gy,baseRoots,rootLen*0.7,wMain*0.4);
    const nR=8+Math.round(G.pulse*10)+Math.min(G.gen,4);
    for(let k=0;k<nR;k++){
      const a=-Math.PI+0.25+(k+rng()*0.6)/nR*(Math.PI-0.5),len=PH*(0.16+rng()*0.2);
      const n=Math.max(5,Math.round(len/(7*u))),P=path(bx,gy-2*u,a,len,n,{wobble:G.wobble*0.5,up:0.02,free:true});
      const t0=0.08+rng()*0.15,t1=t0+0.3,f=fr(k/nR);
      stem(P,3.5*u,2*u,t0,t1,C.leaf2,2);
      const tip=P.pts[n],pa=P.angs[n],pr=(9+rng()*7)*u*(0.8+f.rms*0.5),hairs=[];
      const nh=10+Math.floor(rng()*8);
      for(let h=0;h<nh;h++){const ha=pa+(h/(nh-1)-0.5)*3.4,hl=pr+(6+rng()*10)*u*(0.7+f.rms*0.6);hairs.push([Math.cos(ha),Math.sin(ha),hl,(2+rng()*1.8)*u])}
      const cx=tip[0]+Math.cos(pa)*pr*0.6,cy=tip[1]+Math.sin(pa)*pr*0.6;
      track([[cx-pr*2,cy-pr*2],[cx+pr*2,cy+pr*2]]);
      add(3,t1-0.04,t1+0.1,(ctx,q)=>{const s=easeOut(q);
        ctx.lineWidth=1.1*u;ctx.strokeStyle=C.stem;ctx.globalAlpha=0.8*AM;ctx.beginPath();
        hairs.forEach(h=>{ctx.moveTo(cx,cy);ctx.lineTo(cx+h[0]*h[2]*s,cy+h[1]*h[2]*s)});ctx.stroke();
        ctx.beginPath();ctx.arc(cx,cy,pr*0.6*s,0,TAU);ctx.globalAlpha=Math.max(C.fa,0.3)*AM;ctx.fillStyle=C.leaf;ctx.fill();ctx.globalAlpha=0.85*AM;ctx.stroke();
        hairs.forEach(h=>{ctx.beginPath();ctx.arc(cx+h[0]*h[2]*s,cy+h[1]*h[2]*s,h[3]*s,0,TAU);ctx.globalAlpha=0.9*AM;ctx.fillStyle=C.flower2;ctx.fill();ctx.strokeStyle=C.flower;ctx.stroke()})});
    }
    const nSc=1+Math.round(G.loud*2);
    for(let s=0;s<nSc;s++){
      const len=PH*(0.75+rng()*0.25),n=Math.max(8,Math.round(len/(8*u)));
      const P=path(bx+(s-(nSc-1)/2)*16*u,gy,-Math.PI/2+(s-(nSc-1)/2)*0.25,len,n,{wobble:G.wobble*0.6,up:0.03,curlRamp:(rng()<.5?-1:1)*0.25,fOff:0,fSpan:1});
      const t0=0.15+s*0.06,t1=t0+0.5;
      stem(P,3.5*u,1.5*u,t0,t1);
      const nf=3+Math.floor(rng()*4);
      for(let k=0;k<nf;k++){const q=0.6+k/nf*0.38,i=Math.round(q*n),side=k%2?1:-1,sa=P.angs[i]+side*1.1;
        const ex=P.pts[i][0]+Math.cos(sa)*14*u,ey=P.pts[i][1]+Math.sin(sa)*14*u;
        pedicel(P.pts[i][0],P.pts[i][1],ex,ey,lerp(t0,t1,q));flower(ex,ey,sa,fsize(fr(q),0.65),lerp(t0,t1,q)+0.03,G.flowerType==="bell"?"bell":"daisy")}
    }
  }else{ // bulb
    const rx=(48+G.low*40)*u,ry=rx*1.15,cy=gy-ry*0.35;
    roots(bx,cy+ry*0.9,baseRoots+6,rootLen,4*u);
    const absBulb=X.a>0.45;
    add(2,0.04,0.2,(ctx,q)=>{const s=easeOut(q);ctx.save();ctx.translate(bx,cy);ctx.scale(s,s);
      if(absBulb){ // абстрактная луковица: круг со сдвинутой заливкой и кольцами
        ctx.beginPath();ctx.arc(C.sx,C.sy,rx*1.05,0,TAU);ctx.globalAlpha=Math.max(C.fa,0.3)*AM;ctx.fillStyle=C.flower2;ctx.fill();
        ctx.strokeStyle=C.stem;ctx.lineWidth=1.6*u;ctx.globalAlpha=0.9*AM;
        for(let k=1;k<=4;k++){ctx.beginPath();ctx.arc(0,ry*0.1*(4-k)*0.25,rx*1.05*k/4,0,TAU);ctx.stroke()}
        ctx.restore();return}
      ctx.beginPath();ctx.moveTo(0,-ry*1.15);ctx.bezierCurveTo(rx*0.35,-ry*0.7,rx*1.25,-ry*0.4,rx*1.05,ry*0.35);ctx.bezierCurveTo(rx*0.85,ry*1.0,-rx*0.85,ry*1.0,-rx*1.05,ry*0.35);ctx.bezierCurveTo(-rx*1.25,-ry*0.4,-rx*0.35,-ry*0.7,0,-ry*1.15);ctx.closePath();
      ctx.globalAlpha=Math.max(C.fa,0.3)*AM;ctx.fillStyle=C.flower2;ctx.fill();ctx.globalAlpha=0.9*AM;ctx.strokeStyle=C.stem;ctx.lineWidth=1.6*u;ctx.stroke();
      ctx.globalAlpha=0.4*AM;ctx.lineWidth=u;for(let k=-2;k<=2;k++){ctx.beginPath();ctx.moveTo(0,-ry*1.1);ctx.quadraticCurveTo(k*rx*0.55,-ry*0.1,k*rx*0.3,ry*0.8);ctx.stroke()}
      ctx.restore()});
    track([[bx-rx,cy-ry],[bx+rx,cy+ry]]);
    const ox=bx,oy=cy-ry*1.1;
    const nL=3+Math.round(G.mid*3);
    for(let k=0;k<nL;k++){const side=k%2?1:-1,a=-Math.PI/2+side*(0.2+rng()*0.7),len=PH*(0.32+rng()*0.28),n=Math.max(6,Math.round(len/(8*u)));
      const P=path(ox,oy,a,len,n,{wobble:G.wobble*0.4,droop:0.05+rng()*0.04,free:true});
      stem(P,(14+rng()*8)*u,2*u,0.12+rng()*0.1,0.5+rng()*0.1,C.leaf,3,{col:C.stem,w:1.2*u})}
    const nS=2+Math.round(G.high*3)+Math.min(G.gen-1,2);
    for(let s=0;s<nS;s++){const off=nS>1?(s/(nS-1)-0.5)*2:0,len=PH*(0.7+rng()*0.3)-ry,n=Math.max(8,Math.round(len/(8*u)));
      const P=path(ox+off*6*u,oy,-Math.PI/2+off*0.35,len,n,{wobble:G.wobble*1.4,up:0.03,curl:G.curl*(rng()<.5?-1:1),fOff:0,fSpan:1,free:true});
      const t0=0.18+rng()*0.1,t1=t0+0.5;
      stem(P,4*u,1.5*u,t0,t1);
      for(let i=4;i<n-3;i++){const f=fr(i/n);if(f.onset&&rng()<0.5){const side=rng()<.5?-1:1,sa=P.angs[i]+side*0.9,ex=P.pts[i][0]+Math.cos(sa)*10*u,ey=P.pts[i][1]+Math.sin(sa)*10*u;
        pedicel(P.pts[i][0],P.pts[i][1],ex,ey,lerp(t0,t1,i/n));flower(ex,ey,sa,fsize(f,0.4),lerp(t0,t1,i/n)+0.03,"bud")}}
      flower(P.pts[n][0],P.pts[n][1],P.angs[n],fsize(fr(1),1.2),t1);
    }
  }

  // мутации
  if(G.muts.has("threads")&&anchors.length){
    const nT=6+Math.floor(rng()*8);
    for(let k=0;k<nT;k++){const a=anchors[Math.floor(rng()*anchors.length)];if(a.y>gy-30*u)continue;
      const len=Math.min((40+rng()*200)*u,gy-a.y-10*u),sway=(rng()-.5)*14*u,pts=[];
      for(let i=0;i<=12;i++){const t=i/12;pts.push([a.x+Math.sin(t*Math.PI)*sway,a.y+t*len])}
      add(4,a.t+0.04,a.t+0.16,(ctx,q)=>{strokeLine(ctx,pts,q,C.detail,0.9*u,0.6);if(q>=1){ctx.globalAlpha=AM;ctx.fillStyle=C.flower;ctx.beginPath();ctx.arc(pts[12][0],pts[12][1],3*u,0,TAU);ctx.fill()}});
    }
  }
  if(G.muts.has("drips")){
    flowers.forEach(f=>{if(rng()<0.45)return;const n=1+Math.floor(rng()*2),drops=[];
      for(let k=0;k<n;k++)drops.push([f.x+(rng()-.5)*f.r*0.6,f.y+f.r*(1.1+k*0.9)+rng()*10*u,(3+rng()*3)*u]);
      add(5,f.t+0.08,f.t+0.2,(ctx,q)=>{ctx.globalAlpha=0.9*AM;ctx.fillStyle=f.col;drops.forEach(d=>{const r=d[2]*easeOut(q),y=d[1]-(1-q)*f.r*0.6;
        ctx.beginPath();ctx.moveTo(d[0],y-r*2.4);ctx.quadraticCurveTo(d[0]+r*1.1,y-r*0.2,d[0],y+r);ctx.quadraticCurveTo(d[0]-r*1.1,y-r*0.2,d[0],y-r*2.4);ctx.fill()})});
    });
  }
  if(G.muts.has("spores")){
    const ns=25+Math.round(G.high*40),pad=40*u,list=[];
    for(let k=0;k<ns;k++)list.push([lerp(bbox.x0-pad,bbox.x1+pad,rng()),lerp(Math.max(top*0.5,bbox.y0-pad*2),gy-20*u,Math.pow(rng(),1.4)),(1.4+rng()*4)*u,rng()<0.5,0.82+rng()*0.14]);
    add(5,0.8,1,(ctx,q)=>{const T=lerp(0.8,1,q);ctx.lineWidth=u;list.forEach(s=>{if(T<s[4])return;ctx.beginPath();ctx.arc(s[0],s[1],s[2],0,TAU);
      if(s[3]){ctx.globalAlpha=0.6*AM;ctx.fillStyle=C.flower;ctx.fill()}else{ctx.globalAlpha=0.7*AM;ctx.strokeStyle=C.detail;ctx.stroke()}})});
  }

  // фоновые формы из частот
  {const shapes=[];
    for(let k=0;k<4;k++){const e=gE(fr(k/4+0.1),k*4,k*4+4),x=lerp(bbox.x0,bbox.x1,ar()),y=lerp(bbox.y0,gy,ar()),r=(0.1+ar()*0.18)*PH*(0.6+e*0.8);
      shapes.push({x,y,r,col:k%2?C.flower2:C.leaf2,ring:ar()<0.35})}
    const al=0.2*X.a;
    if(al>0.01)add(-1,0,0.3,(ctx,q)=>{shapes.forEach(s=>{ctx.beginPath();ctx.arc(s.x,s.y,s.r*easeOut(q),0,TAU);
      if(s.ring){ctx.globalAlpha=al*1.6*AM;ctx.strokeStyle=s.col;ctx.lineWidth=6*u;ctx.stroke()}else{ctx.globalAlpha=al*AM;ctx.fillStyle=s.col;ctx.fill()}})});
  }

  ops.sort((a,b)=>a.L-b.L||a.t0-b.t0);
  return {ops,bx,gy,u,W,H,twin:G.muts.has("twin"),flowers:flowers.length,roots:rootCount,cap,textSide};
}

/* ---------- подпись ---------- */
function wrapText(ctx,text,maxW){const words=text.split(" "),lines=[];let line="";
  words.forEach(w=>{const t=line?line+" "+w:w;if(ctx.measureText(t).width>maxW&&line){lines.push(line);line=w}else line=t});if(line)lines.push(line);return lines}

function drawCaption(ctx,M,p,C,info){
  const {W,H}=M;ctx.save();ctx.globalAlpha=p;ctx.fillStyle=C.detail;ctx.textBaseline="alphabetic";
  const serif='"Cormorant Garamond", Georgia, serif',sans='Manrope, system-ui, sans-serif';
  if(M.textSide){
    const x=W*0.6,maxW=W*0.35;let y=H*0.2;
    ctx.textAlign="left";
    ctx.font="600 "+Math.round(H*0.017)+"px "+sans;ctx.globalAlpha=p*0.6;
    ctx.fillText("ОРАНЖЕРЕЯ ПОМЕХ · ОБРАЗЕЦ "+String(info.id).padStart(3,"0"),x,y);
    y+=H*0.085;ctx.globalAlpha=p;
    ctx.font="italic 500 "+Math.round(H*0.062)+"px "+serif;
    wrapText(ctx,info.latin,maxW).forEach(l=>{ctx.fillText(l,x,y);y+=H*0.062});
    ctx.font="500 "+Math.round(H*0.027)+"px "+sans;ctx.fillText(info.ru,x,y);y+=H*0.07;
    ctx.font="400 "+Math.round(H*0.02)+"px "+sans;ctx.globalAlpha=p*0.75;
    info.facts.forEach(f=>{wrapText(ctx,f,maxW).forEach(l=>{ctx.fillText(l,x,y);y+=H*0.03})});
    y+=H*0.02;ctx.globalAlpha=p*0.9;
    wrapText(ctx,info.desc,maxW).forEach(l=>{ctx.fillText(l,x,y);y+=H*0.03});
  }else{
    ctx.textAlign="center";
    ctx.font="italic 500 "+Math.round(H*0.036)+"px "+serif;ctx.fillText(info.latin,M.bx,H*0.945);
    ctx.font="500 "+Math.round(H*0.015)+"px "+sans;ctx.globalAlpha=p*0.7;
    ctx.fillText(info.ru+" · образец "+String(info.id).padStart(3,"0"),M.bx,H*0.975);
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
const state={palette:"sound",format:"square",caption:true,transparent:false,mode:"plant",abstr:0.6,drift:0.3,shift:0.35};
const plants=[];let current=null,uid=0,busy=false,model=null,anim=null;
const cv=$("cv"),frame=$("frame");
const reduceMotion=window.matchMedia&&window.matchMedia("(prefers-reduced-motion: reduce)").matches;

function prepare(p){
  p.G=makeGenes(p);p.names=makeNames(p,p.G);p.desc=describe(p.G);p.V=voiceParams(p,p.G);
}
function makeModel(p){
  const W=state.format==="wide"?2400:2000,H=state.format==="wide"?1350:2000;
  const C=colors(state.palette,p.G);
  const M=buildPlant(p,p.G,C,W,H,state.caption,{a:state.abstr,drift:state.drift,shift:state.shift});
  M.C=C;M.plant=p;
  const bg=document.createElement("canvas");bg.width=W;bg.height=H;
  const b=bg.getContext("2d");b.fillStyle=C.bg;b.fillRect(0,0,W,H);
  const r=mulberry32(99);b.fillStyle=C.detail;b.globalAlpha=0.035;
  for(let i=0;i<2600;i++){const s=1+r()*2.2;b.fillRect(r()*W,r()*H,s,s)}
  M.bg=bg;
  if(state.caption){
    const G=p.G,facts=["Форма роста: "+ARCHE_RU[G.arche],"Высота "+heightCm(p)+" см · цветов "+M.flowers+" · корней "+M.roots,"Поколение "+G.gen];
    if(G.muts.size)facts.push("Мутации: "+[...G.muts].map(k=>MUTS[k].ru).join(", "));
    const info={id:p.id,latin:p.names.latin,ru:p.names.ru,facts,desc:p.desc};
    M.ops.push({L:6,t0:0.72,t1:1,f:(ctx,q)=>drawCaption(ctx,M,q,C,info)});
  }
  return M;
}
const heightCm=p=>Math.round(18+p.G.height*70+(p.gen-1)*6);

function paint(M,T){
  if(cv.width!==M.W||cv.height!==M.H){cv.width=M.W;cv.height=M.H}
  const ctx=cv.getContext("2d");
  ctx.setTransform(1,0,0,1,0,0);ctx.globalAlpha=1;
  if(state.transparent)ctx.clearRect(0,0,M.W,M.H);else ctx.drawImage(M.bg,0,0);
  if(M.twin){ctx.save();ctx.translate(2*M.bx+M.u*70,-M.u*24);ctx.scale(-1,1);AM=0.13;drawOps(ctx,M.ops,T,o=>o.L>=2&&o.L<6);ctx.restore();AM=1}
  drawOps(ctx,M.ops,T,null);
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
  $("pRu").textContent=p.names.ru+" · образец "+String(p.id).padStart(3,"0");
  $("pDesc").textContent=p.desc;
  const rows=[["Из чего выросло",p.sounds.map(s=>s.label).join(" + ")],["Длительность",fmtTime(p.A.duration)],["Форма роста",ARCHE_RU[G.arche]],
    ["Высота",heightCm(p)+" см"],["Цветов",String(model.flowers)],["Поколение",String(G.gen)],["Мутации",G.muts.size?[...G.muts].map(k=>MUTS[k].ru).join(", "):"пока нет"]];
  const dl=$("stats");dl.innerHTML="";
  rows.forEach(([k,v])=>{const dt=document.createElement("dt"),dd=document.createElement("dd");dt.textContent=k;dd.textContent=v;dl.append(dt,dd)});
}

function renderShelf(){
  const box=$("shelf");box.innerHTML="";
  plants.forEach(p=>{
    const b=document.createElement("button");b.className="card";b.setAttribute("aria-current",p===current);
    if(p.thumb){const i=document.createElement("img");i.src=p.thumb;i.alt="";b.append(i)}
    const n=document.createElement("span");n.textContent=p.names.latin;
    const s=document.createElement("small");s.textContent="№"+String(p.id).padStart(3,"0")+" · поколение "+p.gen;
    b.append(n,s);
    b.addEventListener("click",()=>{if(busy||p===current)return;stopVoice();current=p;show(p,false);setNote("Это растение снова перед тобой.")});
    box.append(b);
  });
}

/* ---------- звук на входе ---------- */
async function handleSound(blob,label){
  if(!blob||busy)return;
  busy=true;setBusyUI(true);stopVoice();
  setNote("Слушаю звук…");
  try{
    const {samples,sr}=await decodeToMono(await blob.arrayBuffer());
    const A=analyze(samples,sr);
    if(!A)throw new Error("short");
    const sound={samples,sr,label,A};
    if(state.mode==="feed"&&current){
      if(current.sounds.length>=6){setNote("Это растение уже сыто: шесть звуков максимум. Посади новое.",true);return}
      const p=current;p.sounds.push(sound);p.gen++;p.A=combine(p.sounds.map(s=>s.A));
      const oldArche=p.G.arche;prepare(p);show(p,true);
      setNote(p.G.arche!==oldArche?"Растение съело звук и переродилось. Поколение "+p.gen+".":"Растение съело звук и перерастает. Поколение "+p.gen+".");
    }else{
      const p={id:++uid,sounds:[sound],root:A.seed,variant:0,gen:1,A};
      prepare(p);plants.unshift(p);current=p;show(p,true);
      setNote("Растёт: "+p.names.ru.toLowerCase()+". Нажми «Послушать растение», чтобы услышать, как оно поёт.");
    }
  }catch(err){
    setNote("Не получилось прочитать этот звук. Попробуй mp3 или wav длиннее полсекунды.",true);
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
  if(!navigator.mediaDevices||!navigator.mediaDevices.getUserMedia||!window.MediaRecorder){setNote("Этот браузер не умеет записывать звук. Загрузи файл.",true);return}
  let stream;
  try{stream=await navigator.mediaDevices.getUserMedia({audio:true})}
  catch(e){setNote("Нет доступа к микрофону. Разреши его в браузере или загрузи файл.",true);return}
  const chunks=[];rec=new MediaRecorder(stream);
  rec.ondataavailable=e=>{if(e.data&&e.data.size)chunks.push(e.data)};
  const t0=Date.now();
  const tick=setInterval(()=>{const s=(Date.now()-t0)/1000;micBtn.textContent="Остановить · "+fmtTime(s);if(s>=20&&rec&&rec.state==="recording")rec.stop()},250);
  rec.onstop=()=>{clearInterval(tick);stream.getTracks().forEach(t=>t.stop());rec=null;
    micBtn.textContent="Записать с микрофона";micBtn.classList.remove("rec");
    const blob=new Blob(chunks,{type:(chunks[0]&&chunks[0].type)||"audio/webm"});handleSound(blob,"запись с микрофона")};
  rec.start();micBtn.classList.add("rec");micBtn.textContent="Остановить · 0:00";
  setNote("Записываю. Напой, пошурши, постучи. До 20 секунд.");
});

/* ---------- голос: воспроизведение ---------- */
let AC=null,voice=null,voiceTimer=null;
const listenBtn=$("listen");
function stopVoice(){
  if(voice){voice.nodes.forEach(n=>{try{n.stop()}catch(e){}});try{voice.master.disconnect()}catch(e){}voice=null}
  clearTimeout(voiceTimer);listenBtn.textContent="Послушать растение";frame.classList.remove("singing");
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
  listenBtn.textContent="Остановить";frame.classList.add("singing");
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
  setNote("Если файл не скачался, попробуй другой браузер.",true);
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
  if(!OAC){setNote("Этот браузер не умеет сохранять звук.",true);return}
  busy=true;setBusyUI(true);setNote("Записываю голос растения…");
  try{
    const sr=44100,ctx=new OAC(2,Math.ceil(plan.length*sr),sr);
    buildVoice(ctx,p,V,plan);
    const buf=await new Promise((res,rej)=>{ctx.oncomplete=e=>res(e.renderedBuffer);const r=ctx.startRendering();if(r&&r.then)r.then(res,rej)});
    busy=false;setBusyUI(false);
    await saveBlob(encodeWav(buf),p.names.file+"_golos.wav","Голос сохранён.");
  }catch(e){setNote("Не получилось записать голос.",true)}
  finally{busy=false;setBusyUI(false)}
});

/* ---------- настройки ---------- */
const palWrap=$("palettes");
Object.entries(PALETTES).forEach(([k,p])=>{
  const b=document.createElement("button");b.className="swatch";b.dataset.v=k;b.setAttribute("aria-pressed",k===state.palette);
  const chips=document.createElement("span");chips.className="chips";
  chipsFor(k).forEach(c=>{const i=document.createElement("i");i.style.background=c;chips.append(i)});
  const t=document.createElement("span");t.textContent=p.name;b.append(chips,t);palWrap.append(b);
});
function bindSeg(el,key,after){el.addEventListener("click",e=>{const b=e.target.closest("button");if(!b||b.disabled)return;
  state[key]=b.dataset.v;el.querySelectorAll("button").forEach(x=>x.setAttribute("aria-pressed",x===b));after()})}
const redraw=()=>{if(current)show(current,false)};
bindSeg(palWrap,"palette",redraw);bindSeg($("formats"),"format",redraw);
bindSeg($("modes"),"mode",()=>{$("dropTitle").textContent=state.mode==="feed"?"Подкорми растение звуком":"Выбери аудиофайл";
  setNote(state.mode==="feed"?"Следующий звук достанется этому растению.":"Следующий звук станет новым растением.")});
$("caption").addEventListener("change",e=>{state.caption=e.target.checked;redraw()});
$("transparent").addEventListener("change",e=>{state.transparent=e.target.checked;redraw()});
$("again").addEventListener("click",()=>{if(!current||busy)return;stopVoice();current.variant++;prepare(current);show(current,true);
  setNote("Тот же звук, другая судьба: "+current.names.ru.toLowerCase()+".")});

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
  if(voice){stopVoice();startVoice()}setNote("Голос растения вернулся к исходному.")});

let viewPending=false;
const redrawSoon=()=>{if(viewPending)return;viewPending=true;requestAnimationFrame(()=>{viewPending=false;redraw()});setTimeout(()=>{if(viewPending){viewPending=false;redraw()}},120)};
[{key:"abstr",label:"Абстракция"},{key:"drift",label:"Распад"},{key:"shift",label:"Сдвиг цвета"}].forEach(k=>{
  const kn=makeKnob($("viewKnobs"),{label:k.label,min:0,max:1,fmt:pct(1),onInput:v=>{state[k.key]=v;redrawSoon()}});kn.set(state[k.key],true)});

/* ---------- старт ---------- */
(async function(){
  try{await Promise.race([Promise.all([document.fonts.load('italic 500 40px "Cormorant Garamond"'),document.fonts.load('500 20px Manrope')]),new Promise(r=>setTimeout(r,1500))])}catch(e){}
  const d=demoSound(),A=analyze(d.samples,d.sr);
  const p={id:++uid,sounds:[{samples:d.samples,sr:d.sr,label:"пример",A}],root:A.seed,variant:0,gen:1,A};
  prepare(p);plants.push(p);current=p;show(p,true);
  setNote("Это пример, он вырос из звука колокольчиков и шума. Посади свой звук.");
})();
})();
