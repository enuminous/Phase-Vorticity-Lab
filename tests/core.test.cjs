const test=require('node:test'), assert=require('node:assert/strict'), P=require('../src/core.js');
test('All registered presets pass at multiple windings and orientations',()=>{
  for(const preset of Object.keys(P.PRESETS))for(const winding of [-2,-1,0,1,2])for(const angle of [0,0.7,2.8]){
    const r=P.scan({preset,winding,angle,phase:1.24,frame:0.23});assert.equal(r.decision,'PASS',JSON.stringify(r));
  }
});
for(const fault of ['no-phase','wrong-density','fixed-axis','wrong-frame','fractional'])test('Fault rejected before integration: '+fault,()=>{
  const c=P.config({fault});assert.equal(P.scan(c).decision,'FAIL');assert.throws(()=>P.integrate(c,[[1,1]]),/gate FAIL/);
});
for(const fault of ['missing-boundary','unknown'])test('Unknown obligation blocks integration: '+fault,()=>{
  assert.equal(P.scan({fault}).decision,'UNRESOLVED');assert.throws(()=>P.integrate({fault},[[1,1]]),/UNRESOLVED/);
});
test('Density is U(1) invariant although no explicit phase survives',()=>{
  const a=P.wave(P.config(),[0.2,0.4]),b=P.wave(P.config({phase:2.1}),[0.2,0.4]);
  assert.equal(a.rho*a.rho,b.rho*b.rho);assert.ok(P.difference(a.psi,b.psi)>0.1);
});
test('Core nodes do not divide by amplitude or invent a phase gradient',()=>{
  const c=P.config({preset:'single'});assert.equal(P.wave(c,[0,0]).gradient,null);assert.deepEqual(P.current(c,[0,0]),[0,0]);
});
test('Circulation is 2π a n outside an isolated phase core',()=>{
  for(const n of [-3,-1,0,2])assert.ok(Math.abs(P.circleCirculation(P.config({preset:'single',winding:n}))-P.TAU*n)<1e-10);
});
test('Smooth phase is locally curl-free away from cores',()=>{
  const c=P.config({preset:'dipole'});assert.ok(Math.abs(P.curl(p=>P.wave(c,p).gradient,[0.2,0.6]))<1e-7);
});
test('Current curl is distinct from velocity curl with varying density',()=>{
  const c=P.config({preset:'pair'}),p=[0.31,0.55];assert.ok(Math.abs(P.curl(q=>P.current(c,q),p)-P.omega(c,p))>0.01);
});
test('Regularized circulation approaches quantized circulation outside the core',()=>{
  const c=P.config({preset:'single'}),R=2;const u=P.velocity(c,[R,0]);
  assert.ok(Math.abs(P.TAU*R*u[1]-P.TAU*R*R/(R*R+c.core*c.core))<1e-12);
});
test('Full quadrature is covariant when source nodes and target rotate together',()=>{
  const c=P.config({preset:'dipole',resolution:32}),p=[0.38,1.12],a=0.78;
  const u=P.integrate(c,[p]).velocities[0],v=P.integrate({...c,angle:a},[P.rotate(p,a)]).velocities[0];
  assert.ok(P.difference(v,P.rotate(u,a))<1e-12);
});
test('Finite invalid parameters fail closed',()=>{
  for(const c of [{scale:0},{core:0},{frame:NaN},{resolution:12.5},{extent:Infinity},{winding:5}])assert.equal(P.scan(c).decision,'FAIL');
});
test('Zero winding is a valid zero flow',()=>{
  const r=P.integrate({winding:0},[[0,0],[1,1]]);assert.deepEqual(r.velocities,[[0,0],[0,0]]);
});
test('Invalid query arrays cannot produce an accepted nonfinite field',()=>{
  for(const points of [null,[],[[NaN,0]],[[1]],[[1,2,3]],[[Infinity,0]],[[1e9,0]]])
    assert.throws(()=>P.integrate({},points),/Query points/);
});
