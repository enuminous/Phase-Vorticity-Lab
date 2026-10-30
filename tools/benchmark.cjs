/* Frozen numerical benchmarks. No fitted parameters or randomized selection. */
const P=require('../src/core.js'),fs=require('node:fs'),path=require('node:path');
const probes=[[0.37,1.13],[-1.51,0.73],[1.71,-1.19],[0.21,-2.31]];
const results=[];
for(const preset of ['single','dipole','pair','quadrupole'])for(const resolution of [32,48,80,112]){
  const c=P.config({preset,resolution}),r=P.integrate(c,probes);let e=0,d=0;
  r.velocities.forEach((u,i)=>{const v=P.velocity(c,probes[i]);e+=(u[0]-v[0])**2+(u[1]-v[1])**2;d+=v[0]**2+v[1]**2;});
  results.push({preset,resolution,relativeL2Error:Math.sqrt(e/d),capturedCirculation:r.circulationCaptured,expectedCirculation:r.circulationExpected,gate:r.audit.decision});
}
const fine=results.filter(r=>r.resolution===112);
const threshold=0.12,passed=fine.every(r=>r.relativeL2Error<threshold);
const report={schema:'PVL-benchmark-1',scope:'Four fixed probes, four preset fields; finite domain half-width 4, core 0.32, scale 1.',criterion:'Every 112×112 case has relative L2 error < 0.12 at the four frozen probes. Monotonic refinement is NOT required or claimed.',threshold,passed,probes,results};
fs.mkdirSync(path.join(__dirname,'../evidence'),{recursive:true});fs.writeFileSync(path.join(__dirname,'../evidence/numerical-benchmark.json'),JSON.stringify(report,null,2)+'\n');
console.table(results);console.log('Fine-grid accuracy criterion:',passed?'PASS':'FAIL');process.exitCode=passed?0:1;
