/* PVL-001: deterministic, dimensionless 2D kinematic model. No dependencies. */
(function (root, factory) {
  const api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.PVL = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';
  const TAU = 2 * Math.PI;
  const DEFAULT = Object.freeze({preset:'dipole', winding:1, core:0.32, phase:0,
    angle:0, frame:0, scale:1, extent:4, resolution:48, fault:'none',
    boundary:'whole-plane-decay', representation:'polar-vortex'});
  const PRESETS = {
    single: [[0,0,1]], dipole:[[-0.9,0,1],[0.9,0,-1]],
    pair:[[-0.9,0,1],[0.9,0,1]],
    quadrupole:[[-1,-1,1],[1,-1,-1],[1,1,1],[-1,1,-1]]
  };
  const FAULTS=['none','no-phase','wrong-density','fixed-axis','wrong-frame','fractional','missing-boundary','unknown'];
  const rotate=(p,a)=>[Math.cos(a)*p[0]-Math.sin(a)*p[1], Math.sin(a)*p[0]+Math.cos(a)*p[1]];
  const norm=p=>Math.hypot(...p);
  const difference=(a,b)=>norm(a.map((v,i)=>v-b[i])) / Math.max(1,norm(a),norm(b));
  const config=x=>Object.assign({},DEFAULT,x);
  function vortices(c) {
    return PRESETS[c.preset].map(([x,y,n])=>({p:rotate([x,y],c.angle), n:n*c.winding*(c.fault==='fractional'?0.5:1)}));
  }
  function wave(c,p) {
    let rho=1, theta=c.phase, gx=0, gy=0, node=false;
    for (const v of vortices(c)) {
      const dx=p[0]-v.p[0],dy=p[1]-v.p[1],r2=dx*dx+dy*dy;
      if (v.n===0) continue;
      if (r2<1e-24) {rho=0; node=true; continue;}
      const local=rotate([dx,dy],-c.angle);
      rho *= Math.pow(Math.sqrt(r2/(r2+c.core*c.core)),Math.abs(v.n));
      theta += v.n*Math.atan2(local[1],local[0]);
      gx -= v.n*dy/r2; gy += v.n*dx/r2;
    }
    const psi=c.fault==='no-phase'?[rho,0]:[rho*Math.cos(theta),rho*Math.sin(theta)];
    return {rho,theta,psi,gradient:node?null:[gx,gy],node};
  }
  function current(c,p) {
    const w=wave(c,p);
    if(w.node) return [0,0]; // continuous extension for nonzero integer winding
    const density=c.fault==='wrong-density'?w.rho:w.rho*w.rho;
    let j=w.gradient.map(g=>c.scale*density*g);
    if(c.fault==='fixed-axis') j=[j[0]*1.35,j[1]];
    return j;
  }
  function waveCurrent(c,p,h=1e-5) {
    const w=wave(c,p).psi;
    return [0,1].map(i=>{
      const a=p.slice(), b=p.slice(); a[i]+=h; b[i]-=h;
      const wa=wave(c,a).psi,wb=wave(c,b).psi;
      return c.scale*(w[0]*(wa[1]-wb[1])-w[1]*(wa[0]-wb[0]))/(2*h);
    });
  }
  function velocity(c,p) {
    let u=[0,0];
    for(const v of vortices(c)) {
      const x=p[0]-v.p[0],y=p[1]-v.p[1],d=x*x+y*y+c.core*c.core;
      u[0]-=c.scale*v.n*y/d; u[1]+=c.scale*v.n*x/d;
    }
    if(c.fault==='fixed-axis') u[0]*=1.35;
    return u;
  }
  function omega(c,p) {
    return vortices(c).reduce((s,v)=>{
      const d=(p[0]-v.p[0])**2+(p[1]-v.p[1])**2+c.core*c.core;
      return s+2*c.scale*v.n*c.core*c.core/(d*d);
    },0);
  }
  function relative(c,p,u=velocity(c,p)) {
    const f=c.frame*(c.fault==='wrong-frame'?2:1);
    return [u[0]+f*p[1],u[1]-f*p[0]];
  }
  function curl(fn,p,h=1e-5) {
    return (fn([p[0]+h,p[1]])[1]-fn([p[0]-h,p[1]])[1]
      -fn([p[0],p[1]+h])[0]+fn([p[0],p[1]-h])[0])/(2*h);
  }
  function kernel(c,r) {
    const r2=r[0]*r[0]+r[1]*r[1];
    if(r2<1e-24) return [0,0]; // symmetric self-cell midpoint convention
    return [-(c.fault==='fixed-axis'?1.35:1)*r[1]/(TAU*r2),r[0]/(TAU*r2)];
  }
  function scan(input) {
    const c=config(input),checks=[];
    const add=(id,label,status,value,limit,detail)=>checks.push({id,label,status,value,limit,detail});
    const finite=['winding','core','phase','angle','frame','scale','extent','resolution'].every(k=>Number.isFinite(c[k]));
    const bounds=finite && c.core>=0.08&&c.core<=1&&c.scale>0&&c.scale<=10&&c.extent>=3&&c.extent<=12&&
      Number.isInteger(c.resolution)&&c.resolution>=16&&c.resolution<=160&&Math.abs(c.winding)<=4&&Math.abs(c.frame)<=2;
    add('domain','Domain and conventions',bounds?'PASS':'FAIL',null,null,'Fixed dimensionless convention: length L₀, time T₀, scale ℏ/m in L₀²/T₀. Positive core and scale; finite, bounded inputs. This does not infer units from arbitrary expressions.');
    const known=Boolean(PRESETS[c.preset])&&FAULTS.includes(c.fault)&&c.representation==='polar-vortex'&&c.fault!=='unknown';
    add('representation','Known representation',known?'PASS':'UNRESOLVED',null,null,'Only this registered polar-vortex family is evaluated. Unknown symbolic forms are not silently accepted.');
    if(!bounds||!known) return finish();
    const integer=Number.isInteger(c.winding)&&vortices(c).every(v=>Number.isInteger(v.n));
    add('winding','Single-valued wave',integer?'PASS':'FAIL',null,null,'Integer winding; phase undefined at zero amplitude. Fractional winding is rejected.');
    const boundary=c.boundary==='whole-plane-decay'&&c.fault!=='missing-boundary';
    add('boundary','Reconstruction domain',boundary?'PASS':'UNRESOLVED',null,null,'Whole-plane decaying vortex field; finite-square quadrature approximation. Frame velocity added separately.');
    const probes=[[0.37,0.61],[-1.43,0.47],[1.24,-0.83],[0.21,-1.73]];
    let phaseErr=0,currentErr=0,identityErr=0,rotationErr=0,kernelErr=0,curlErr=0,frameErr=0;
    for(const p of probes) {
      const w=wave(c,p),j=current(c,p),shifted=config({...c,phase:c.phase+0.731});
      phaseErr=Math.max(phaseErr,difference(wave(shifted,p).psi,rotate(w.psi,0.731)));
      currentErr=Math.max(currentErr,difference(current(shifted,p),j));
      identityErr=Math.max(identityErr,difference(j,waveCurrent(c,p)));
      curlErr=Math.max(curlErr,Math.abs(curl(q=>velocity(c,q),p)-omega(c,p))/Math.max(1,Math.abs(omega(c,p))));
      const frameC=config({...c,frame:0.37});
      frameErr=Math.max(frameErr,Math.abs(curl(q=>relative(frameC,q),p)-(omega(c,p)-0.74)));
      for(const a of [0.29,1.13,2.4]) {
        const cc=config({...c,angle:c.angle+a}),q=rotate(p,a);
        rotationErr=Math.max(rotationErr,difference(current(cc,q),rotate(j,a)),difference(velocity(cc,q),rotate(velocity(c,p),a)),difference(wave(cc,q).psi,w.psi));
        kernelErr=Math.max(kernelErr,difference(kernel(c,q),rotate(kernel(c,p),a)));
      }
    }
    const numeric=(id,label,v,t,detail)=>add(id,label,v<=t?'PASS':'FAIL',v,t,detail);
    numeric('phase','Global U(1) phase',phaseErr,1e-10,'ψ → eⁱᵅψ. An invariant density does not need an explicit phase factor.');
    numeric('current','Current invariance',currentErr,1e-10,'J is unchanged by a constant phase shift; no local gauge field is modeled.');
    numeric('identity','Madelung current identity',identityErr,2e-6,'J = a Im(conj ψ ∇ψ) = a ρ²∇θ, checked using independent finite differences away from cores.');
    numeric('rotation','Spatial SO(2) covariance',rotationErr,1e-10,'Rotate source geometry, phase chart and observation point together; vector outputs rotate. Finite tests, not a universal proof.');
    numeric('kernel','Biot–Savart kernel covariance',kernelErr,1e-10,'The same kernel used for integration is checked under three proper planar rotations.');
    numeric('curl','Velocity–vorticity agreement',curlErr,2e-6,'Finite-difference curl of the regularized velocity agrees with the chosen smooth blob vorticity.');
    numeric('frame','Rotating-frame normalization',frameErr,2e-6,'u_rel = u − Ω×r; curl(u_rel) = ω − 2Ω. A nonzero frame probe prevents a zero-Ω false pass.');
    return finish();
    function finish(){const decision=checks.some(x=>x.status==='FAIL')?'FAIL':checks.some(x=>x.status==='UNRESOLVED')?'UNRESOLVED':'PASS';return {schema:'PVL-scan-1',decision,eligible:decision==='PASS',checks,config:c,scope:'Finite numerical checks of registered 2D model; not Lean execution or physical validation.'};}
  }
  function sources(c,n=c.resolution) {
    const a=2*c.extent/n,out=[];
    for(let iy=0;iy<n;iy++) for(let ix=0;ix<n;ix++) {
      const p=rotate([-c.extent+(ix+0.5)*a,-c.extent+(iy+0.5)*a],c.angle);
      out.push({p,weight:omega(c,p)*a*a});
    }
    return out;
  }
  function sum(c,p,src) {
    let x=0,y=0;
    for(const s of src){const k=kernel(c,[p[0]-s.p[0],p[1]-s.p[1]]);x+=k[0]*s.weight;y+=k[1]*s.weight;}
    return [x,y];
  }
  function integrate(input,points) {
    const c=config(input),audit=scan(c);
    if(!audit.eligible){const e=new Error('Pre-integration gate '+audit.decision);e.audit=audit;throw e;}
    if(!Array.isArray(points)||points.length===0||points.length>16384||!points.every(p=>Array.isArray(p)&&p.length===2&&p.every(x=>Number.isFinite(x)&&Math.abs(x)<=1e6)))
      throw new TypeError('Query points must contain 1–16384 finite coordinate pairs with |coordinate| ≤ 1e6.');
    const src=sources(c),velocities=points.map(p=>sum(c,p,src));
    return {schema:'PVL-integration-1',config:c,audit,points,velocities,
      relative:points.map((p,i)=>relative(c,p,velocities[i])),
      circulationCaptured:src.reduce((s,v)=>s+v.weight,0),
      circulationExpected:TAU*c.scale*vortices(c).reduce((s,v)=>s+v.n,0),
      sourceCount:src.length,method:'Whole-plane kernel; midpoint quadrature on a finite rotated square; zero symmetric self-cell contribution.'};
  }
  function circleCirculation(c,r=2.5,n=1024) {
    let out=0;
    for(let i=0;i<n;i++){const t=TAU*(i+0.5)/n,p=[r*Math.cos(t),r*Math.sin(t)],w=wave(c,p);if(w.gradient)out+=c.scale*(w.gradient[0]*-r*Math.sin(t)+w.gradient[1]*r*Math.cos(t))*TAU/n;}
    return out;
  }
  return {TAU,DEFAULT,PRESETS,FAULTS,config,rotate,norm,difference,vortices,wave,current,waveCurrent,velocity,omega,relative,curl,kernel,scan,sources,sum,integrate,circleCirculation};
});
