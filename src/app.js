(function(){
  'use strict';
  const P=window.PVL, $=id=>document.getElementById(id), canvas=$('field'),ctx=canvas.getContext('2d');
  const bg=document.createElement('canvas'),bc=bg.getContext('2d');
  const ids=['preset','winding','core','phase','angle','frame','resolution','fault'];
  let c=P.config(),audit=P.scan(c),result=null,layer='phase',running=false,particles=[],lastTime=0,hover=null,dirty=true;
  const gridN=31,probes=[[0.37,1.13],[-1.51,0.73],[1.71,-1.19],[0.21,-2.31]];
  function read(){return P.config({preset:$('preset').value,winding:+$('winding').value,core:+$('core').value,phase:+$('phase').value*Math.PI/180,angle:+$('angle').value*Math.PI/180,frame:+$('frame').value,resolution:+$('resolution').value,fault:$('fault').value});}
  function fmt(x){if(!Number.isFinite(x))return '—';if(x===0)return '0';return Math.abs(x)<0.001?x.toExponential(2):x.toFixed(3);}
  function settings(){
    c=read();audit=P.scan(c);result=null;running=false;particles=[];
    for(const id of ['winding','core','phase','angle','frame'])$(id+'Out').textContent=id==='winding'?c.winding:id==='phase'||id==='angle'?$(id).value+'°':c[id].toFixed(2);
    $('play').disabled=true;$('play').textContent='▶ Tracers';$('csv').disabled=true;
    $('errorMetric').textContent='—';$('errorSub').textContent='Run integration for comparison';
    $('canvasStatus').textContent=audit.eligible?'Candidate · not yet integrated':'Integration blocked · '+audit.decision;
    $('fieldNotice').textContent=audit.eligible?'Arrows show the analytic regularized velocity. Run integration to replace them with the reconstructed field.':'The candidate is shown for inspection. The gate has blocked Biot–Savart integration; no previous result is being reused.';
    renderAudit();dirty=true;
  }
  function renderAudit(){
    $('gateMetric').textContent=audit.decision==='PASS'?'ACCEPTED':audit.decision==='FAIL'?'REJECTED':'UNRESOLVED';
    $('gateMetric').className=audit.decision==='PASS'?'passText':audit.decision==='FAIL'?'failText':'warnText';
    $('gateSub').textContent=audit.eligible?'Finite model checks passed':'Integration is blocked';
    const passed=audit.checks.filter(x=>x.status==='PASS').length;
    $('checkCount').textContent=passed+' / '+audit.checks.length+' PASS';
    $('checks').replaceChildren();
    for(const q of audit.checks){
      const row=document.createElement('details');row.className='check';
      const s=document.createElement('summary'),t=document.createElement('span'),status=document.createElement('span');t.textContent=q.label;status.className='badge '+q.status.toLowerCase();status.textContent=q.status;s.append(t,status);row.append(s);
      const p=document.createElement('p');p.textContent=q.detail;row.append(p);
      if(q.value!==null){const code=document.createElement('code');code.textContent=q.value.toExponential(2)+' / limit '+q.limit.toExponential(0);row.append(code);}
      if(q.status!=='PASS')row.open=true;$('checks').append(row);
    }
    const rot=audit.checks.find(x=>x.id==='rotation');$('covMetric').textContent=rot?fmt(rot.value):'—';
    $('circulationMetric').textContent=fmt(P.circleCirculation(c)/P.TAU)+' × 2π';
    $('run').disabled=!audit.eligible;
  }
  function gridPoints(){const points=[];for(let j=0;j<gridN;j++)for(let i=0;i<gridN;i++)points.push([-c.extent+2*c.extent*i/(gridN-1),-c.extent+2*c.extent*j/(gridN-1)]);return points;}
  async function run(){
    $('run').disabled=true;$('run').textContent='Integrating…';
    await new Promise(resolve=>setTimeout(resolve,20));
    try{
      const start=performance.now(),points=gridPoints();
      result=P.integrate(c,points.concat(probes));
      result.elapsedMs=performance.now()-start;result.gridN=gridN;
      let err=0,den=0;
      probes.forEach((p,i)=>{const u=result.velocities[gridN*gridN+i],v=P.velocity(c,p);err+=(u[0]-v[0])**2+(u[1]-v[1])**2;den+=v[0]**2+v[1]**2;});
      result.probeRelativeError=den?Math.sqrt(err/den):0;
      $('errorMetric').textContent=(100*result.probeRelativeError).toFixed(2)+'%';
      $('errorMetric').className=result.probeRelativeError>0.12?'failText':result.probeRelativeError>0.05?'warnText':'passText';
      $('errorSub').textContent=result.probeRelativeError>0.05?'Large probe error · refine the source grid':'4 probes · vs whole-plane analytic blob';
      $('canvasStatus').textContent='Integrated · '+result.sourceCount.toLocaleString()+' source cells';
      $('fieldNotice').textContent='Arrows and tracers use the reconstructed '+(c.frame?'relative':'laboratory')+' velocity. '+result.elapsedMs.toFixed(0)+' ms · captured signed circulation '+fmt(result.circulationCaptured)+' / expected '+fmt(result.circulationExpected)+'. Finite-domain and grid errors remain.';
      $('csv').disabled=false;$('play').disabled=false;running=true;$('play').textContent='Ⅱ Pause';seedParticles();
    }catch(e){result=null;running=false;audit=e.audit||P.scan(c);$('canvasStatus').textContent='Integration blocked';$('fieldNotice').textContent=e.message;renderAudit();}
    $('run').innerHTML='Run gated integration <span>↗</span>';$('run').disabled=!audit.eligible;dirty=true;
  }
  function interpolated(p){
    if(!result)return P.relative(c,p);
    const fx=(p[0]+c.extent)/(2*c.extent)*(gridN-1),fy=(p[1]+c.extent)/(2*c.extent)*(gridN-1);
    if(fx<0||fy<0||fx>=gridN-1||fy>=gridN-1)return [0,0];
    const x=Math.floor(fx),y=Math.floor(fy),dx=fx-x,dy=fy-y,u=[0,0];
    for(let j=0;j<2;j++)for(let i=0;i<2;i++){const w=(i?dx:1-dx)*(j?dy:1-dy),v=result.relative[(y+j)*gridN+x+i];u[0]+=w*v[0];u[1]+=w*v[1];}
    return u;
  }
  let seed=43821;
  function random(){seed=(1664525*seed+1013904223)>>>0;return seed/4294967296;}
  function fresh(){return {p:[(random()*2-1)*c.extent,(random()*2-1)*c.extent],trail:[],age:random()*10};}
  function seedParticles(){seed=43821;particles=Array.from({length:330},fresh);}
  function xy(p){return [(p[0]/(2*c.extent)+0.5)*canvas.width,(0.5-p[1]/(2*c.extent))*canvas.height];}
  function color(h,s,v){h=((h%1)+1)%1;const i=Math.floor(h*6),f=h*6-i,p=v*(1-s),q=v*(1-f*s),t=v*(1-(1-f)*s);return [[v,t,p],[q,v,p],[p,v,t],[p,q,v],[t,p,v],[v,p,q]][i%6].map(x=>Math.round(255*x));}
  function background(){
    bg.width=240;bg.height=Math.round(240*canvas.height/canvas.width);const img=bc.createImageData(bg.width,bg.height);
    for(let j=0;j<bg.height;j++)for(let i=0;i<bg.width;i++){
      const p=[(i/bg.width*2-1)*c.extent,(1-j/bg.height*2)*c.extent],w=P.wave(c,p);let rgb;
      if(layer==='phase')rgb=color(Math.atan2(w.psi[1],w.psi[0])/P.TAU+0.5,.54,.08+.27*w.rho);
      else if(layer==='density'){const d=w.rho*w.rho;rgb=[10+20*d,17+75*d,24+77*d];}
      else if(layer==='omega'){const v=P.omega(c,p)-2*c.frame,t=Math.min(1,Math.log1p(Math.abs(v))/3.2);rgb=v>=0?[13+196*t,22+105*t,29+33*t]:[13+24*t,22+100*t,29+186*t];}
      else {const speed=P.norm(interpolated(p)),v=Math.min(1,speed/3.8);rgb=[9+40*v,18+156*v,29+119*v];}
      const k=(j*bg.width+i)*4;img.data[k]=rgb[0];img.data[k+1]=rgb[1];img.data[k+2]=rgb[2];img.data[k+3]=255;
    }
    bc.putImageData(img,0,0);dirty=false;
  }
  function draw(t){
    const rect=canvas.getBoundingClientRect(),ratio=Math.min(2,window.devicePixelRatio||1),cw=Math.round(rect.width*ratio),ch=Math.round(rect.height*ratio);
    if(cw!==canvas.width||ch!==canvas.height){canvas.width=cw;canvas.height=ch;dirty=true;}
    if(dirty)background();ctx.drawImage(bg,0,0,canvas.width,canvas.height);
    ctx.lineWidth=ratio;ctx.strokeStyle='#9bbcc00c';ctx.beginPath();
    for(let i=1;i<8;i++){ctx.moveTo(canvas.width*i/8,0);ctx.lineTo(canvas.width*i/8,canvas.height);ctx.moveTo(0,canvas.height*i/8);ctx.lineTo(canvas.width,canvas.height*i/8);}ctx.stroke();
    // Velocity arrows are distinguished from the phase-current probe below.
    for(let j=1;j<14;j++)for(let i=1;i<14;i++){
      const p=[(i/14*2-1)*c.extent,(j/14*2-1)*c.extent],u=interpolated(p),m=P.norm(u);if(m<1e-8)continue;
      const a=xy(p),len=Math.min(16,4+7*Math.log1p(m))*ratio,dx=u[0]/m*len,dy=-u[1]/m*len;
      ctx.strokeStyle='#c8eee059';ctx.lineWidth=.8*ratio;ctx.beginPath();ctx.moveTo(a[0]-dx*.4,a[1]-dy*.4);ctx.lineTo(a[0]+dx*.6,a[1]+dy*.6);ctx.lineTo(a[0]+dx*.25-dy*.18,a[1]+dy*.25+dx*.18);ctx.moveTo(a[0]+dx*.6,a[1]+dy*.6);ctx.lineTo(a[0]+dx*.25+dy*.18,a[1]+dy*.25-dx*.18);ctx.stroke();
    }
    const dt=Math.min(.033,(t-lastTime)/1000||0);lastTime=t;
    if(result)for(let i=0;i<particles.length;i++){
      let q=particles[i];
      if(running){
        const v=interpolated(q.p),mid=[q.p[0]+.5*dt*v[0],q.p[1]+.5*dt*v[1]],v2=interpolated(mid);q.p=[q.p[0]+dt*v2[0],q.p[1]+dt*v2[1]];q.age+=dt;
        if(Math.abs(q.p[0])>=c.extent-.01||Math.abs(q.p[1])>=c.extent-.01||q.age>16){q=fresh();q.age=0;particles[i]=q;}
        q.trail.push(q.p.slice());if(q.trail.length>14)q.trail.shift();
      }
      if(q.trail.length){ctx.beginPath();q.trail.forEach((p,k)=>{const z=xy(p);k?ctx.lineTo(...z):ctx.moveTo(...z);});ctx.strokeStyle='#bdf6de82';ctx.lineWidth=.8*ratio;ctx.stroke();const z=xy(q.p);ctx.fillStyle='#ddfff3b0';ctx.fillRect(z[0],z[1],1.5*ratio,1.5*ratio);}
    }
    for(const v of P.vortices(c)){
      if(v.n===0)continue;const p=xy(v.p);ctx.strokeStyle=v.n>0?'#8febd0aa':'#f3b37daa';ctx.lineWidth=ratio;ctx.setLineDash([3*ratio,3*ratio]);ctx.beginPath();ctx.ellipse(p[0],p[1],c.core/(2*c.extent)*canvas.width,c.core/(2*c.extent)*canvas.height,0,0,P.TAU);ctx.stroke();ctx.setLineDash([]);ctx.fillStyle='#08151ee8';ctx.beginPath();ctx.arc(p[0],p[1],10*ratio,0,P.TAU);ctx.fill();ctx.fillStyle=v.n>0?'#a7f5df':'#ffc28d';ctx.textAlign='center';ctx.textBaseline='middle';ctx.font=10*ratio+'px monospace';ctx.fillText((v.n>0?'+':'')+v.n,p[0],p[1]);
    }
    if(hover){const p=xy(hover);ctx.strokeStyle='#d4e6e270';ctx.beginPath();ctx.moveTo(p[0]-9*ratio,p[1]);ctx.lineTo(p[0]+9*ratio,p[1]);ctx.moveTo(p[0],p[1]-9*ratio);ctx.lineTo(p[0],p[1]+9*ratio);ctx.stroke();}
    requestAnimationFrame(draw);
  }
  function download(name,text,type){const a=document.createElement('a'),url=URL.createObjectURL(new Blob([text],{type}));a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);}
  ids.forEach(id=>$(id).addEventListener('input',settings));$('run').addEventListener('click',run);
  $('reset').addEventListener('click',()=>{for(const id of ids)$(id).value=id==='phase'||id==='angle'?0:P.DEFAULT[id];settings();run();});
  $('play').addEventListener('click',()=>{running=!running;$('play').textContent=running?'Ⅱ Pause':'▶ Tracers';});
  document.querySelectorAll('[data-layer]').forEach(b=>b.addEventListener('click',()=>{
    layer=b.dataset.layer;document.querySelectorAll('[data-layer]').forEach(q=>{q.classList.toggle('active',q===b);q.setAttribute('aria-pressed',q===b?'true':'false');});
    const labels={phase:['−π','+π','ψ = ρ exp(iθ)'],omega:['negative','positive','ω_rel = ω − 2Ω'],density:['0','1','n = |ψ|² = ρ²'],speed:['0','3.8+','|u_rel| · L₀/T₀']};
    $('legendLow').textContent=labels[layer][0];$('legendHigh').textContent=labels[layer][1];$('canvasNote').textContent=labels[layer][2];
    $('legendBar').style.background=layer==='phase'?'linear-gradient(90deg,#68e0e6,#a286ff,#ff879d,#ffc47d,#8ce2b4,#68e0e6)':layer==='omega'?'linear-gradient(90deg,#258bc3,#111923,#f3ae72)':'linear-gradient(90deg,#0a151d,#55bda5)';dirty=true;
  }));
  canvas.addEventListener('pointermove',e=>{const r=canvas.getBoundingClientRect();hover=[((e.clientX-r.left)/r.width*2-1)*c.extent,(1-(e.clientY-r.top)/r.height*2)*c.extent];const w=P.wave(c,hover);$('position').textContent=hover.map(x=>x.toFixed(2)).join(', ');$('density').textContent=fmt(w.rho*w.rho);$('vorticity').textContent=fmt(P.omega(c,hover)-2*c.frame);$('current').textContent=fmt(P.norm(P.current(c,hover)));});canvas.addEventListener('pointerleave',()=>hover=null);
  $('export').addEventListener('click',()=>download('PVL-001-evidence.json',JSON.stringify({version:'0.1.0',createdAt:new Date().toISOString(),audit,integration:result,upstream:{commit:'6e85c9e558652f5033c55d70f33077eff7a9fd89',ci:'https://github.com/enuminous/Monolithic-102-Zoo-Lean4/actions/runs/40600670063',status:'Recorded upstream CI success; no local Lean rebuild'},limits:['No general symbolic parser','Finite symmetry probes only','2D kinematic fluid reconstruction','No cosmological or quantum-dynamics validation']},null,2),'application/json'));
  $('csv').addEventListener('click',()=>{if(!result)return;const rows=['x,y,u_x,u_y,u_rel_x,u_rel_y,omega_lab,omega_rel,rho_squared'];result.points.forEach((p,i)=>rows.push([...p,...result.velocities[i],...result.relative[i],P.omega(c,p),P.omega(c,p)-2*c.frame,P.wave(c,p).rho**2].join(',')));download('PVL-001-field.csv',rows.join('\n')+'\n','text/csv');});
  $('aboutButton').addEventListener('click',()=>$('about').showModal());$('closeAbout').addEventListener('click',()=>$('about').close());
  window.PVLApp={getState:()=>({config:c,audit,result,layer,running}),run,settings};
  settings();requestAnimationFrame(draw);setTimeout(run,60);
})();
