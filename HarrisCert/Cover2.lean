module

public import HarrisCert.Kernel
public import HarrisCert.Leaves.L21
public import HarrisCert.Leaves.L22
public import HarrisCert.Leaves.L23
public import HarrisCert.Leaves.L24
public import HarrisCert.Leaves.L25
public import HarrisCert.Leaves.L26
public import HarrisCert.Leaves.L27
public import HarrisCert.Leaves.L28
public import HarrisCert.Leaves.L29
public import HarrisCert.Leaves.L30
public import HarrisCert.Leaves.L31
public import HarrisCert.Leaves.L32

/-! Leaves 1313 … 1969 cover their boxes. -/

@[expose] public section

namespace Harris

theorem cr_1313_1314 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1314) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1313 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1313_ok
theorem cr_1314_1315 (k : ℕ) (h1 : 1314 ≤ k) (h2 : k < 1315) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1314 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1314_ok
theorem cr_1313_1315 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1315) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1314 then cr_1313_1314 k h1 h else cr_1314_1315 k (by omega) h2
theorem cr_1315_1316 (k : ℕ) (h1 : 1315 ≤ k) (h2 : k < 1316) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1315 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1315_ok
theorem cr_1316_1317 (k : ℕ) (h1 : 1316 ≤ k) (h2 : k < 1317) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1316 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1316_ok
theorem cr_1317_1318 (k : ℕ) (h1 : 1317 ≤ k) (h2 : k < 1318) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1317 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1317_ok
theorem cr_1316_1318 (k : ℕ) (h1 : 1316 ≤ k) (h2 : k < 1318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1317 then cr_1316_1317 k h1 h else cr_1317_1318 k (by omega) h2
theorem cr_1315_1318 (k : ℕ) (h1 : 1315 ≤ k) (h2 : k < 1318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1316 then cr_1315_1316 k h1 h else cr_1316_1318 k (by omega) h2
theorem cr_1313_1318 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1315 then cr_1313_1315 k h1 h else cr_1315_1318 k (by omega) h2
theorem cr_1318_1319 (k : ℕ) (h1 : 1318 ≤ k) (h2 : k < 1319) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1318 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1318_ok
theorem cr_1319_1320 (k : ℕ) (h1 : 1319 ≤ k) (h2 : k < 1320) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1319 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1319_ok
theorem cr_1318_1320 (k : ℕ) (h1 : 1318 ≤ k) (h2 : k < 1320) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1319 then cr_1318_1319 k h1 h else cr_1319_1320 k (by omega) h2
theorem cr_1320_1321 (k : ℕ) (h1 : 1320 ≤ k) (h2 : k < 1321) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1320 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1320_ok
theorem cr_1321_1322 (k : ℕ) (h1 : 1321 ≤ k) (h2 : k < 1322) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1321 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1321_ok
theorem cr_1322_1323 (k : ℕ) (h1 : 1322 ≤ k) (h2 : k < 1323) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1322 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1322_ok
theorem cr_1321_1323 (k : ℕ) (h1 : 1321 ≤ k) (h2 : k < 1323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1322 then cr_1321_1322 k h1 h else cr_1322_1323 k (by omega) h2
theorem cr_1320_1323 (k : ℕ) (h1 : 1320 ≤ k) (h2 : k < 1323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1321 then cr_1320_1321 k h1 h else cr_1321_1323 k (by omega) h2
theorem cr_1318_1323 (k : ℕ) (h1 : 1318 ≤ k) (h2 : k < 1323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1320 then cr_1318_1320 k h1 h else cr_1320_1323 k (by omega) h2
theorem cr_1313_1323 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1318 then cr_1313_1318 k h1 h else cr_1318_1323 k (by omega) h2
theorem cr_1323_1324 (k : ℕ) (h1 : 1323 ≤ k) (h2 : k < 1324) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1323 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1323_ok
theorem cr_1324_1325 (k : ℕ) (h1 : 1324 ≤ k) (h2 : k < 1325) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1324 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1324_ok
theorem cr_1323_1325 (k : ℕ) (h1 : 1323 ≤ k) (h2 : k < 1325) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1324 then cr_1323_1324 k h1 h else cr_1324_1325 k (by omega) h2
theorem cr_1325_1326 (k : ℕ) (h1 : 1325 ≤ k) (h2 : k < 1326) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1325 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1325_ok
theorem cr_1326_1327 (k : ℕ) (h1 : 1326 ≤ k) (h2 : k < 1327) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1326 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1326_ok
theorem cr_1327_1328 (k : ℕ) (h1 : 1327 ≤ k) (h2 : k < 1328) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1327 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1327_ok
theorem cr_1326_1328 (k : ℕ) (h1 : 1326 ≤ k) (h2 : k < 1328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1327 then cr_1326_1327 k h1 h else cr_1327_1328 k (by omega) h2
theorem cr_1325_1328 (k : ℕ) (h1 : 1325 ≤ k) (h2 : k < 1328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1326 then cr_1325_1326 k h1 h else cr_1326_1328 k (by omega) h2
theorem cr_1323_1328 (k : ℕ) (h1 : 1323 ≤ k) (h2 : k < 1328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1325 then cr_1323_1325 k h1 h else cr_1325_1328 k (by omega) h2
theorem cr_1328_1329 (k : ℕ) (h1 : 1328 ≤ k) (h2 : k < 1329) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1328 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1328_ok
theorem cr_1329_1330 (k : ℕ) (h1 : 1329 ≤ k) (h2 : k < 1330) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1329 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1329_ok
theorem cr_1328_1330 (k : ℕ) (h1 : 1328 ≤ k) (h2 : k < 1330) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1329 then cr_1328_1329 k h1 h else cr_1329_1330 k (by omega) h2
theorem cr_1330_1331 (k : ℕ) (h1 : 1330 ≤ k) (h2 : k < 1331) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1330 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1330_ok
theorem cr_1331_1332 (k : ℕ) (h1 : 1331 ≤ k) (h2 : k < 1332) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1331 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1331_ok
theorem cr_1332_1333 (k : ℕ) (h1 : 1332 ≤ k) (h2 : k < 1333) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1332 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1332_ok
theorem cr_1331_1333 (k : ℕ) (h1 : 1331 ≤ k) (h2 : k < 1333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1332 then cr_1331_1332 k h1 h else cr_1332_1333 k (by omega) h2
theorem cr_1330_1333 (k : ℕ) (h1 : 1330 ≤ k) (h2 : k < 1333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1331 then cr_1330_1331 k h1 h else cr_1331_1333 k (by omega) h2
theorem cr_1328_1333 (k : ℕ) (h1 : 1328 ≤ k) (h2 : k < 1333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1330 then cr_1328_1330 k h1 h else cr_1330_1333 k (by omega) h2
theorem cr_1323_1333 (k : ℕ) (h1 : 1323 ≤ k) (h2 : k < 1333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1328 then cr_1323_1328 k h1 h else cr_1328_1333 k (by omega) h2
theorem cr_1313_1333 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1323 then cr_1313_1323 k h1 h else cr_1323_1333 k (by omega) h2
theorem cr_1333_1334 (k : ℕ) (h1 : 1333 ≤ k) (h2 : k < 1334) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1333 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1333_ok
theorem cr_1334_1335 (k : ℕ) (h1 : 1334 ≤ k) (h2 : k < 1335) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1334 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1334_ok
theorem cr_1333_1335 (k : ℕ) (h1 : 1333 ≤ k) (h2 : k < 1335) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1334 then cr_1333_1334 k h1 h else cr_1334_1335 k (by omega) h2
theorem cr_1335_1336 (k : ℕ) (h1 : 1335 ≤ k) (h2 : k < 1336) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1335 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1335_ok
theorem cr_1336_1337 (k : ℕ) (h1 : 1336 ≤ k) (h2 : k < 1337) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1336 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1336_ok
theorem cr_1337_1338 (k : ℕ) (h1 : 1337 ≤ k) (h2 : k < 1338) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1337 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1337_ok
theorem cr_1336_1338 (k : ℕ) (h1 : 1336 ≤ k) (h2 : k < 1338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1337 then cr_1336_1337 k h1 h else cr_1337_1338 k (by omega) h2
theorem cr_1335_1338 (k : ℕ) (h1 : 1335 ≤ k) (h2 : k < 1338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1336 then cr_1335_1336 k h1 h else cr_1336_1338 k (by omega) h2
theorem cr_1333_1338 (k : ℕ) (h1 : 1333 ≤ k) (h2 : k < 1338) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1335 then cr_1333_1335 k h1 h else cr_1335_1338 k (by omega) h2
theorem cr_1338_1339 (k : ℕ) (h1 : 1338 ≤ k) (h2 : k < 1339) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1338 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1338_ok
theorem cr_1339_1340 (k : ℕ) (h1 : 1339 ≤ k) (h2 : k < 1340) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1339 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1339_ok
theorem cr_1338_1340 (k : ℕ) (h1 : 1338 ≤ k) (h2 : k < 1340) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1339 then cr_1338_1339 k h1 h else cr_1339_1340 k (by omega) h2
theorem cr_1340_1341 (k : ℕ) (h1 : 1340 ≤ k) (h2 : k < 1341) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1340 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1340_ok
theorem cr_1341_1342 (k : ℕ) (h1 : 1341 ≤ k) (h2 : k < 1342) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1341 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1341_ok
theorem cr_1342_1343 (k : ℕ) (h1 : 1342 ≤ k) (h2 : k < 1343) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1342 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1342_ok
theorem cr_1341_1343 (k : ℕ) (h1 : 1341 ≤ k) (h2 : k < 1343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1342 then cr_1341_1342 k h1 h else cr_1342_1343 k (by omega) h2
theorem cr_1340_1343 (k : ℕ) (h1 : 1340 ≤ k) (h2 : k < 1343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1341 then cr_1340_1341 k h1 h else cr_1341_1343 k (by omega) h2
theorem cr_1338_1343 (k : ℕ) (h1 : 1338 ≤ k) (h2 : k < 1343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1340 then cr_1338_1340 k h1 h else cr_1340_1343 k (by omega) h2
theorem cr_1333_1343 (k : ℕ) (h1 : 1333 ≤ k) (h2 : k < 1343) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1338 then cr_1333_1338 k h1 h else cr_1338_1343 k (by omega) h2
theorem cr_1343_1344 (k : ℕ) (h1 : 1343 ≤ k) (h2 : k < 1344) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1343 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1343_ok
theorem cr_1344_1345 (k : ℕ) (h1 : 1344 ≤ k) (h2 : k < 1345) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1344 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1344_ok
theorem cr_1343_1345 (k : ℕ) (h1 : 1343 ≤ k) (h2 : k < 1345) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1344 then cr_1343_1344 k h1 h else cr_1344_1345 k (by omega) h2
theorem cr_1345_1346 (k : ℕ) (h1 : 1345 ≤ k) (h2 : k < 1346) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1345 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1345_ok
theorem cr_1346_1347 (k : ℕ) (h1 : 1346 ≤ k) (h2 : k < 1347) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1346 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1346_ok
theorem cr_1347_1348 (k : ℕ) (h1 : 1347 ≤ k) (h2 : k < 1348) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1347 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1347_ok
theorem cr_1346_1348 (k : ℕ) (h1 : 1346 ≤ k) (h2 : k < 1348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1347 then cr_1346_1347 k h1 h else cr_1347_1348 k (by omega) h2
theorem cr_1345_1348 (k : ℕ) (h1 : 1345 ≤ k) (h2 : k < 1348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1346 then cr_1345_1346 k h1 h else cr_1346_1348 k (by omega) h2
theorem cr_1343_1348 (k : ℕ) (h1 : 1343 ≤ k) (h2 : k < 1348) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1345 then cr_1343_1345 k h1 h else cr_1345_1348 k (by omega) h2
theorem cr_1348_1349 (k : ℕ) (h1 : 1348 ≤ k) (h2 : k < 1349) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1348 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1348_ok
theorem cr_1349_1350 (k : ℕ) (h1 : 1349 ≤ k) (h2 : k < 1350) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1349 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1349_ok
theorem cr_1350_1351 (k : ℕ) (h1 : 1350 ≤ k) (h2 : k < 1351) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1350 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1350_ok
theorem cr_1349_1351 (k : ℕ) (h1 : 1349 ≤ k) (h2 : k < 1351) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1350 then cr_1349_1350 k h1 h else cr_1350_1351 k (by omega) h2
theorem cr_1348_1351 (k : ℕ) (h1 : 1348 ≤ k) (h2 : k < 1351) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1349 then cr_1348_1349 k h1 h else cr_1349_1351 k (by omega) h2
theorem cr_1351_1352 (k : ℕ) (h1 : 1351 ≤ k) (h2 : k < 1352) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1351 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1351_ok
theorem cr_1352_1353 (k : ℕ) (h1 : 1352 ≤ k) (h2 : k < 1353) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1352 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1352_ok
theorem cr_1353_1354 (k : ℕ) (h1 : 1353 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1353 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1353_ok
theorem cr_1352_1354 (k : ℕ) (h1 : 1352 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1353 then cr_1352_1353 k h1 h else cr_1353_1354 k (by omega) h2
theorem cr_1351_1354 (k : ℕ) (h1 : 1351 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1352 then cr_1351_1352 k h1 h else cr_1352_1354 k (by omega) h2
theorem cr_1348_1354 (k : ℕ) (h1 : 1348 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1351 then cr_1348_1351 k h1 h else cr_1351_1354 k (by omega) h2
theorem cr_1343_1354 (k : ℕ) (h1 : 1343 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1348 then cr_1343_1348 k h1 h else cr_1348_1354 k (by omega) h2
theorem cr_1333_1354 (k : ℕ) (h1 : 1333 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1343 then cr_1333_1343 k h1 h else cr_1343_1354 k (by omega) h2
theorem cr_1313_1354 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1333 then cr_1313_1333 k h1 h else cr_1333_1354 k (by omega) h2
theorem cr_1354_1355 (k : ℕ) (h1 : 1354 ≤ k) (h2 : k < 1355) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1354 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1354_ok
theorem cr_1355_1356 (k : ℕ) (h1 : 1355 ≤ k) (h2 : k < 1356) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1355 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1355_ok
theorem cr_1354_1356 (k : ℕ) (h1 : 1354 ≤ k) (h2 : k < 1356) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1355 then cr_1354_1355 k h1 h else cr_1355_1356 k (by omega) h2
theorem cr_1356_1357 (k : ℕ) (h1 : 1356 ≤ k) (h2 : k < 1357) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1356 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1356_ok
theorem cr_1357_1358 (k : ℕ) (h1 : 1357 ≤ k) (h2 : k < 1358) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1357 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1357_ok
theorem cr_1358_1359 (k : ℕ) (h1 : 1358 ≤ k) (h2 : k < 1359) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1358 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1358_ok
theorem cr_1357_1359 (k : ℕ) (h1 : 1357 ≤ k) (h2 : k < 1359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1358 then cr_1357_1358 k h1 h else cr_1358_1359 k (by omega) h2
theorem cr_1356_1359 (k : ℕ) (h1 : 1356 ≤ k) (h2 : k < 1359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1357 then cr_1356_1357 k h1 h else cr_1357_1359 k (by omega) h2
theorem cr_1354_1359 (k : ℕ) (h1 : 1354 ≤ k) (h2 : k < 1359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1356 then cr_1354_1356 k h1 h else cr_1356_1359 k (by omega) h2
theorem cr_1359_1360 (k : ℕ) (h1 : 1359 ≤ k) (h2 : k < 1360) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1359 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1359_ok
theorem cr_1360_1361 (k : ℕ) (h1 : 1360 ≤ k) (h2 : k < 1361) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1360 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1360_ok
theorem cr_1359_1361 (k : ℕ) (h1 : 1359 ≤ k) (h2 : k < 1361) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1360 then cr_1359_1360 k h1 h else cr_1360_1361 k (by omega) h2
theorem cr_1361_1362 (k : ℕ) (h1 : 1361 ≤ k) (h2 : k < 1362) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1361 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1361_ok
theorem cr_1362_1363 (k : ℕ) (h1 : 1362 ≤ k) (h2 : k < 1363) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1362 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1362_ok
theorem cr_1363_1364 (k : ℕ) (h1 : 1363 ≤ k) (h2 : k < 1364) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1363 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1363_ok
theorem cr_1362_1364 (k : ℕ) (h1 : 1362 ≤ k) (h2 : k < 1364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1363 then cr_1362_1363 k h1 h else cr_1363_1364 k (by omega) h2
theorem cr_1361_1364 (k : ℕ) (h1 : 1361 ≤ k) (h2 : k < 1364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1362 then cr_1361_1362 k h1 h else cr_1362_1364 k (by omega) h2
theorem cr_1359_1364 (k : ℕ) (h1 : 1359 ≤ k) (h2 : k < 1364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1361 then cr_1359_1361 k h1 h else cr_1361_1364 k (by omega) h2
theorem cr_1354_1364 (k : ℕ) (h1 : 1354 ≤ k) (h2 : k < 1364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1359 then cr_1354_1359 k h1 h else cr_1359_1364 k (by omega) h2
theorem cr_1364_1365 (k : ℕ) (h1 : 1364 ≤ k) (h2 : k < 1365) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1364 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1364_ok
theorem cr_1365_1366 (k : ℕ) (h1 : 1365 ≤ k) (h2 : k < 1366) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1365 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1365_ok
theorem cr_1364_1366 (k : ℕ) (h1 : 1364 ≤ k) (h2 : k < 1366) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1365 then cr_1364_1365 k h1 h else cr_1365_1366 k (by omega) h2
theorem cr_1366_1367 (k : ℕ) (h1 : 1366 ≤ k) (h2 : k < 1367) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1366 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1366_ok
theorem cr_1367_1368 (k : ℕ) (h1 : 1367 ≤ k) (h2 : k < 1368) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1367 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1367_ok
theorem cr_1368_1369 (k : ℕ) (h1 : 1368 ≤ k) (h2 : k < 1369) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1368 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1368_ok
theorem cr_1367_1369 (k : ℕ) (h1 : 1367 ≤ k) (h2 : k < 1369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1368 then cr_1367_1368 k h1 h else cr_1368_1369 k (by omega) h2
theorem cr_1366_1369 (k : ℕ) (h1 : 1366 ≤ k) (h2 : k < 1369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1367 then cr_1366_1367 k h1 h else cr_1367_1369 k (by omega) h2
theorem cr_1364_1369 (k : ℕ) (h1 : 1364 ≤ k) (h2 : k < 1369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1366 then cr_1364_1366 k h1 h else cr_1366_1369 k (by omega) h2
theorem cr_1369_1370 (k : ℕ) (h1 : 1369 ≤ k) (h2 : k < 1370) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1369 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1369_ok
theorem cr_1370_1371 (k : ℕ) (h1 : 1370 ≤ k) (h2 : k < 1371) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1370 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1370_ok
theorem cr_1369_1371 (k : ℕ) (h1 : 1369 ≤ k) (h2 : k < 1371) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1370 then cr_1369_1370 k h1 h else cr_1370_1371 k (by omega) h2
theorem cr_1371_1372 (k : ℕ) (h1 : 1371 ≤ k) (h2 : k < 1372) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1371 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1371_ok
theorem cr_1372_1373 (k : ℕ) (h1 : 1372 ≤ k) (h2 : k < 1373) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1372 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1372_ok
theorem cr_1373_1374 (k : ℕ) (h1 : 1373 ≤ k) (h2 : k < 1374) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1373 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1373_ok
theorem cr_1372_1374 (k : ℕ) (h1 : 1372 ≤ k) (h2 : k < 1374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1373 then cr_1372_1373 k h1 h else cr_1373_1374 k (by omega) h2
theorem cr_1371_1374 (k : ℕ) (h1 : 1371 ≤ k) (h2 : k < 1374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1372 then cr_1371_1372 k h1 h else cr_1372_1374 k (by omega) h2
theorem cr_1369_1374 (k : ℕ) (h1 : 1369 ≤ k) (h2 : k < 1374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1371 then cr_1369_1371 k h1 h else cr_1371_1374 k (by omega) h2
theorem cr_1364_1374 (k : ℕ) (h1 : 1364 ≤ k) (h2 : k < 1374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1369 then cr_1364_1369 k h1 h else cr_1369_1374 k (by omega) h2
theorem cr_1354_1374 (k : ℕ) (h1 : 1354 ≤ k) (h2 : k < 1374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1364 then cr_1354_1364 k h1 h else cr_1364_1374 k (by omega) h2
theorem cr_1374_1375 (k : ℕ) (h1 : 1374 ≤ k) (h2 : k < 1375) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1374 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1374_ok
theorem cr_1375_1376 (k : ℕ) (h1 : 1375 ≤ k) (h2 : k < 1376) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1375 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1375_ok
theorem cr_1374_1376 (k : ℕ) (h1 : 1374 ≤ k) (h2 : k < 1376) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1375 then cr_1374_1375 k h1 h else cr_1375_1376 k (by omega) h2
theorem cr_1376_1377 (k : ℕ) (h1 : 1376 ≤ k) (h2 : k < 1377) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1376 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1376_ok
theorem cr_1377_1378 (k : ℕ) (h1 : 1377 ≤ k) (h2 : k < 1378) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1377 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1377_ok
theorem cr_1378_1379 (k : ℕ) (h1 : 1378 ≤ k) (h2 : k < 1379) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1378 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1378_ok
theorem cr_1377_1379 (k : ℕ) (h1 : 1377 ≤ k) (h2 : k < 1379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1378 then cr_1377_1378 k h1 h else cr_1378_1379 k (by omega) h2
theorem cr_1376_1379 (k : ℕ) (h1 : 1376 ≤ k) (h2 : k < 1379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1377 then cr_1376_1377 k h1 h else cr_1377_1379 k (by omega) h2
theorem cr_1374_1379 (k : ℕ) (h1 : 1374 ≤ k) (h2 : k < 1379) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1376 then cr_1374_1376 k h1 h else cr_1376_1379 k (by omega) h2
theorem cr_1379_1380 (k : ℕ) (h1 : 1379 ≤ k) (h2 : k < 1380) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1379 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1379_ok
theorem cr_1380_1381 (k : ℕ) (h1 : 1380 ≤ k) (h2 : k < 1381) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1380 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1380_ok
theorem cr_1379_1381 (k : ℕ) (h1 : 1379 ≤ k) (h2 : k < 1381) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1380 then cr_1379_1380 k h1 h else cr_1380_1381 k (by omega) h2
theorem cr_1381_1382 (k : ℕ) (h1 : 1381 ≤ k) (h2 : k < 1382) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1381 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1381_ok
theorem cr_1382_1383 (k : ℕ) (h1 : 1382 ≤ k) (h2 : k < 1383) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1382 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1382_ok
theorem cr_1383_1384 (k : ℕ) (h1 : 1383 ≤ k) (h2 : k < 1384) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1383 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1383_ok
theorem cr_1382_1384 (k : ℕ) (h1 : 1382 ≤ k) (h2 : k < 1384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1383 then cr_1382_1383 k h1 h else cr_1383_1384 k (by omega) h2
theorem cr_1381_1384 (k : ℕ) (h1 : 1381 ≤ k) (h2 : k < 1384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1382 then cr_1381_1382 k h1 h else cr_1382_1384 k (by omega) h2
theorem cr_1379_1384 (k : ℕ) (h1 : 1379 ≤ k) (h2 : k < 1384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1381 then cr_1379_1381 k h1 h else cr_1381_1384 k (by omega) h2
theorem cr_1374_1384 (k : ℕ) (h1 : 1374 ≤ k) (h2 : k < 1384) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1379 then cr_1374_1379 k h1 h else cr_1379_1384 k (by omega) h2
theorem cr_1384_1385 (k : ℕ) (h1 : 1384 ≤ k) (h2 : k < 1385) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1384 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1384_ok
theorem cr_1385_1386 (k : ℕ) (h1 : 1385 ≤ k) (h2 : k < 1386) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1385 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1385_ok
theorem cr_1384_1386 (k : ℕ) (h1 : 1384 ≤ k) (h2 : k < 1386) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1385 then cr_1384_1385 k h1 h else cr_1385_1386 k (by omega) h2
theorem cr_1386_1387 (k : ℕ) (h1 : 1386 ≤ k) (h2 : k < 1387) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1386 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1386_ok
theorem cr_1387_1388 (k : ℕ) (h1 : 1387 ≤ k) (h2 : k < 1388) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1387 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1387_ok
theorem cr_1388_1389 (k : ℕ) (h1 : 1388 ≤ k) (h2 : k < 1389) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1388 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1388_ok
theorem cr_1387_1389 (k : ℕ) (h1 : 1387 ≤ k) (h2 : k < 1389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1388 then cr_1387_1388 k h1 h else cr_1388_1389 k (by omega) h2
theorem cr_1386_1389 (k : ℕ) (h1 : 1386 ≤ k) (h2 : k < 1389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1387 then cr_1386_1387 k h1 h else cr_1387_1389 k (by omega) h2
theorem cr_1384_1389 (k : ℕ) (h1 : 1384 ≤ k) (h2 : k < 1389) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1386 then cr_1384_1386 k h1 h else cr_1386_1389 k (by omega) h2
theorem cr_1389_1390 (k : ℕ) (h1 : 1389 ≤ k) (h2 : k < 1390) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1389 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1389_ok
theorem cr_1390_1391 (k : ℕ) (h1 : 1390 ≤ k) (h2 : k < 1391) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1390 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1390_ok
theorem cr_1391_1392 (k : ℕ) (h1 : 1391 ≤ k) (h2 : k < 1392) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1391 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1391_ok
theorem cr_1390_1392 (k : ℕ) (h1 : 1390 ≤ k) (h2 : k < 1392) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1391 then cr_1390_1391 k h1 h else cr_1391_1392 k (by omega) h2
theorem cr_1389_1392 (k : ℕ) (h1 : 1389 ≤ k) (h2 : k < 1392) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1390 then cr_1389_1390 k h1 h else cr_1390_1392 k (by omega) h2
theorem cr_1392_1393 (k : ℕ) (h1 : 1392 ≤ k) (h2 : k < 1393) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1392 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1392_ok
theorem cr_1393_1394 (k : ℕ) (h1 : 1393 ≤ k) (h2 : k < 1394) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1393 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1393_ok
theorem cr_1394_1395 (k : ℕ) (h1 : 1394 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1394 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1394_ok
theorem cr_1393_1395 (k : ℕ) (h1 : 1393 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1394 then cr_1393_1394 k h1 h else cr_1394_1395 k (by omega) h2
theorem cr_1392_1395 (k : ℕ) (h1 : 1392 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1393 then cr_1392_1393 k h1 h else cr_1393_1395 k (by omega) h2
theorem cr_1389_1395 (k : ℕ) (h1 : 1389 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1392 then cr_1389_1392 k h1 h else cr_1392_1395 k (by omega) h2
theorem cr_1384_1395 (k : ℕ) (h1 : 1384 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1389 then cr_1384_1389 k h1 h else cr_1389_1395 k (by omega) h2
theorem cr_1374_1395 (k : ℕ) (h1 : 1374 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1384 then cr_1374_1384 k h1 h else cr_1384_1395 k (by omega) h2
theorem cr_1354_1395 (k : ℕ) (h1 : 1354 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1374 then cr_1354_1374 k h1 h else cr_1374_1395 k (by omega) h2
theorem cr_1313_1395 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1354 then cr_1313_1354 k h1 h else cr_1354_1395 k (by omega) h2
theorem cr_1395_1396 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1396) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1395 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1395_ok
theorem cr_1396_1397 (k : ℕ) (h1 : 1396 ≤ k) (h2 : k < 1397) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1396 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1396_ok
theorem cr_1395_1397 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1397) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1396 then cr_1395_1396 k h1 h else cr_1396_1397 k (by omega) h2
theorem cr_1397_1398 (k : ℕ) (h1 : 1397 ≤ k) (h2 : k < 1398) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1397 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1397_ok
theorem cr_1398_1399 (k : ℕ) (h1 : 1398 ≤ k) (h2 : k < 1399) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1398 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1398_ok
theorem cr_1399_1400 (k : ℕ) (h1 : 1399 ≤ k) (h2 : k < 1400) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1399 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1399_ok
theorem cr_1398_1400 (k : ℕ) (h1 : 1398 ≤ k) (h2 : k < 1400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1399 then cr_1398_1399 k h1 h else cr_1399_1400 k (by omega) h2
theorem cr_1397_1400 (k : ℕ) (h1 : 1397 ≤ k) (h2 : k < 1400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1398 then cr_1397_1398 k h1 h else cr_1398_1400 k (by omega) h2
theorem cr_1395_1400 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1397 then cr_1395_1397 k h1 h else cr_1397_1400 k (by omega) h2
theorem cr_1400_1401 (k : ℕ) (h1 : 1400 ≤ k) (h2 : k < 1401) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1400 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1400_ok
theorem cr_1401_1402 (k : ℕ) (h1 : 1401 ≤ k) (h2 : k < 1402) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1401 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1401_ok
theorem cr_1400_1402 (k : ℕ) (h1 : 1400 ≤ k) (h2 : k < 1402) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1401 then cr_1400_1401 k h1 h else cr_1401_1402 k (by omega) h2
theorem cr_1402_1403 (k : ℕ) (h1 : 1402 ≤ k) (h2 : k < 1403) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1402 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1402_ok
theorem cr_1403_1404 (k : ℕ) (h1 : 1403 ≤ k) (h2 : k < 1404) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1403 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1403_ok
theorem cr_1404_1405 (k : ℕ) (h1 : 1404 ≤ k) (h2 : k < 1405) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1404 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1404_ok
theorem cr_1403_1405 (k : ℕ) (h1 : 1403 ≤ k) (h2 : k < 1405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1404 then cr_1403_1404 k h1 h else cr_1404_1405 k (by omega) h2
theorem cr_1402_1405 (k : ℕ) (h1 : 1402 ≤ k) (h2 : k < 1405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1403 then cr_1402_1403 k h1 h else cr_1403_1405 k (by omega) h2
theorem cr_1400_1405 (k : ℕ) (h1 : 1400 ≤ k) (h2 : k < 1405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1402 then cr_1400_1402 k h1 h else cr_1402_1405 k (by omega) h2
theorem cr_1395_1405 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1400 then cr_1395_1400 k h1 h else cr_1400_1405 k (by omega) h2
theorem cr_1405_1406 (k : ℕ) (h1 : 1405 ≤ k) (h2 : k < 1406) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1405 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1405_ok
theorem cr_1406_1407 (k : ℕ) (h1 : 1406 ≤ k) (h2 : k < 1407) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1406 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1406_ok
theorem cr_1405_1407 (k : ℕ) (h1 : 1405 ≤ k) (h2 : k < 1407) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1406 then cr_1405_1406 k h1 h else cr_1406_1407 k (by omega) h2
theorem cr_1407_1408 (k : ℕ) (h1 : 1407 ≤ k) (h2 : k < 1408) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1407 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1407_ok
theorem cr_1408_1409 (k : ℕ) (h1 : 1408 ≤ k) (h2 : k < 1409) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1408 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1408_ok
theorem cr_1409_1410 (k : ℕ) (h1 : 1409 ≤ k) (h2 : k < 1410) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1409 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1409_ok
theorem cr_1408_1410 (k : ℕ) (h1 : 1408 ≤ k) (h2 : k < 1410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1409 then cr_1408_1409 k h1 h else cr_1409_1410 k (by omega) h2
theorem cr_1407_1410 (k : ℕ) (h1 : 1407 ≤ k) (h2 : k < 1410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1408 then cr_1407_1408 k h1 h else cr_1408_1410 k (by omega) h2
theorem cr_1405_1410 (k : ℕ) (h1 : 1405 ≤ k) (h2 : k < 1410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1407 then cr_1405_1407 k h1 h else cr_1407_1410 k (by omega) h2
theorem cr_1410_1411 (k : ℕ) (h1 : 1410 ≤ k) (h2 : k < 1411) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1410 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1410_ok
theorem cr_1411_1412 (k : ℕ) (h1 : 1411 ≤ k) (h2 : k < 1412) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1411 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1411_ok
theorem cr_1410_1412 (k : ℕ) (h1 : 1410 ≤ k) (h2 : k < 1412) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1411 then cr_1410_1411 k h1 h else cr_1411_1412 k (by omega) h2
theorem cr_1412_1413 (k : ℕ) (h1 : 1412 ≤ k) (h2 : k < 1413) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1412 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1412_ok
theorem cr_1413_1414 (k : ℕ) (h1 : 1413 ≤ k) (h2 : k < 1414) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1413 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1413_ok
theorem cr_1414_1415 (k : ℕ) (h1 : 1414 ≤ k) (h2 : k < 1415) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1414 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1414_ok
theorem cr_1413_1415 (k : ℕ) (h1 : 1413 ≤ k) (h2 : k < 1415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1414 then cr_1413_1414 k h1 h else cr_1414_1415 k (by omega) h2
theorem cr_1412_1415 (k : ℕ) (h1 : 1412 ≤ k) (h2 : k < 1415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1413 then cr_1412_1413 k h1 h else cr_1413_1415 k (by omega) h2
theorem cr_1410_1415 (k : ℕ) (h1 : 1410 ≤ k) (h2 : k < 1415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1412 then cr_1410_1412 k h1 h else cr_1412_1415 k (by omega) h2
theorem cr_1405_1415 (k : ℕ) (h1 : 1405 ≤ k) (h2 : k < 1415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1410 then cr_1405_1410 k h1 h else cr_1410_1415 k (by omega) h2
theorem cr_1395_1415 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1405 then cr_1395_1405 k h1 h else cr_1405_1415 k (by omega) h2
theorem cr_1415_1416 (k : ℕ) (h1 : 1415 ≤ k) (h2 : k < 1416) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1415 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1415_ok
theorem cr_1416_1417 (k : ℕ) (h1 : 1416 ≤ k) (h2 : k < 1417) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1416 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1416_ok
theorem cr_1415_1417 (k : ℕ) (h1 : 1415 ≤ k) (h2 : k < 1417) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1416 then cr_1415_1416 k h1 h else cr_1416_1417 k (by omega) h2
theorem cr_1417_1418 (k : ℕ) (h1 : 1417 ≤ k) (h2 : k < 1418) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1417 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1417_ok
theorem cr_1418_1419 (k : ℕ) (h1 : 1418 ≤ k) (h2 : k < 1419) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1418 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1418_ok
theorem cr_1419_1420 (k : ℕ) (h1 : 1419 ≤ k) (h2 : k < 1420) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1419 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1419_ok
theorem cr_1418_1420 (k : ℕ) (h1 : 1418 ≤ k) (h2 : k < 1420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1419 then cr_1418_1419 k h1 h else cr_1419_1420 k (by omega) h2
theorem cr_1417_1420 (k : ℕ) (h1 : 1417 ≤ k) (h2 : k < 1420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1418 then cr_1417_1418 k h1 h else cr_1418_1420 k (by omega) h2
theorem cr_1415_1420 (k : ℕ) (h1 : 1415 ≤ k) (h2 : k < 1420) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1417 then cr_1415_1417 k h1 h else cr_1417_1420 k (by omega) h2
theorem cr_1420_1421 (k : ℕ) (h1 : 1420 ≤ k) (h2 : k < 1421) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1420 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1420_ok
theorem cr_1421_1422 (k : ℕ) (h1 : 1421 ≤ k) (h2 : k < 1422) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1421 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1421_ok
theorem cr_1420_1422 (k : ℕ) (h1 : 1420 ≤ k) (h2 : k < 1422) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1421 then cr_1420_1421 k h1 h else cr_1421_1422 k (by omega) h2
theorem cr_1422_1423 (k : ℕ) (h1 : 1422 ≤ k) (h2 : k < 1423) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1422 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1422_ok
theorem cr_1423_1424 (k : ℕ) (h1 : 1423 ≤ k) (h2 : k < 1424) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1423 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1423_ok
theorem cr_1424_1425 (k : ℕ) (h1 : 1424 ≤ k) (h2 : k < 1425) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1424 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1424_ok
theorem cr_1423_1425 (k : ℕ) (h1 : 1423 ≤ k) (h2 : k < 1425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1424 then cr_1423_1424 k h1 h else cr_1424_1425 k (by omega) h2
theorem cr_1422_1425 (k : ℕ) (h1 : 1422 ≤ k) (h2 : k < 1425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1423 then cr_1422_1423 k h1 h else cr_1423_1425 k (by omega) h2
theorem cr_1420_1425 (k : ℕ) (h1 : 1420 ≤ k) (h2 : k < 1425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1422 then cr_1420_1422 k h1 h else cr_1422_1425 k (by omega) h2
theorem cr_1415_1425 (k : ℕ) (h1 : 1415 ≤ k) (h2 : k < 1425) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1420 then cr_1415_1420 k h1 h else cr_1420_1425 k (by omega) h2
theorem cr_1425_1426 (k : ℕ) (h1 : 1425 ≤ k) (h2 : k < 1426) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1425 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1425_ok
theorem cr_1426_1427 (k : ℕ) (h1 : 1426 ≤ k) (h2 : k < 1427) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1426 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1426_ok
theorem cr_1425_1427 (k : ℕ) (h1 : 1425 ≤ k) (h2 : k < 1427) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1426 then cr_1425_1426 k h1 h else cr_1426_1427 k (by omega) h2
theorem cr_1427_1428 (k : ℕ) (h1 : 1427 ≤ k) (h2 : k < 1428) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1427 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1427_ok
theorem cr_1428_1429 (k : ℕ) (h1 : 1428 ≤ k) (h2 : k < 1429) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1428 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1428_ok
theorem cr_1429_1430 (k : ℕ) (h1 : 1429 ≤ k) (h2 : k < 1430) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1429 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1429_ok
theorem cr_1428_1430 (k : ℕ) (h1 : 1428 ≤ k) (h2 : k < 1430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1429 then cr_1428_1429 k h1 h else cr_1429_1430 k (by omega) h2
theorem cr_1427_1430 (k : ℕ) (h1 : 1427 ≤ k) (h2 : k < 1430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1428 then cr_1427_1428 k h1 h else cr_1428_1430 k (by omega) h2
theorem cr_1425_1430 (k : ℕ) (h1 : 1425 ≤ k) (h2 : k < 1430) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1427 then cr_1425_1427 k h1 h else cr_1427_1430 k (by omega) h2
theorem cr_1430_1431 (k : ℕ) (h1 : 1430 ≤ k) (h2 : k < 1431) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1430 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1430_ok
theorem cr_1431_1432 (k : ℕ) (h1 : 1431 ≤ k) (h2 : k < 1432) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1431 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1431_ok
theorem cr_1432_1433 (k : ℕ) (h1 : 1432 ≤ k) (h2 : k < 1433) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1432 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1432_ok
theorem cr_1431_1433 (k : ℕ) (h1 : 1431 ≤ k) (h2 : k < 1433) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1432 then cr_1431_1432 k h1 h else cr_1432_1433 k (by omega) h2
theorem cr_1430_1433 (k : ℕ) (h1 : 1430 ≤ k) (h2 : k < 1433) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1431 then cr_1430_1431 k h1 h else cr_1431_1433 k (by omega) h2
theorem cr_1433_1434 (k : ℕ) (h1 : 1433 ≤ k) (h2 : k < 1434) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1433 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1433_ok
theorem cr_1434_1435 (k : ℕ) (h1 : 1434 ≤ k) (h2 : k < 1435) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1434 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1434_ok
theorem cr_1435_1436 (k : ℕ) (h1 : 1435 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1435 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1435_ok
theorem cr_1434_1436 (k : ℕ) (h1 : 1434 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1435 then cr_1434_1435 k h1 h else cr_1435_1436 k (by omega) h2
theorem cr_1433_1436 (k : ℕ) (h1 : 1433 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1434 then cr_1433_1434 k h1 h else cr_1434_1436 k (by omega) h2
theorem cr_1430_1436 (k : ℕ) (h1 : 1430 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1433 then cr_1430_1433 k h1 h else cr_1433_1436 k (by omega) h2
theorem cr_1425_1436 (k : ℕ) (h1 : 1425 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1430 then cr_1425_1430 k h1 h else cr_1430_1436 k (by omega) h2
theorem cr_1415_1436 (k : ℕ) (h1 : 1415 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1425 then cr_1415_1425 k h1 h else cr_1425_1436 k (by omega) h2
theorem cr_1395_1436 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1415 then cr_1395_1415 k h1 h else cr_1415_1436 k (by omega) h2
theorem cr_1436_1437 (k : ℕ) (h1 : 1436 ≤ k) (h2 : k < 1437) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1436 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1436_ok
theorem cr_1437_1438 (k : ℕ) (h1 : 1437 ≤ k) (h2 : k < 1438) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1437 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1437_ok
theorem cr_1436_1438 (k : ℕ) (h1 : 1436 ≤ k) (h2 : k < 1438) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1437 then cr_1436_1437 k h1 h else cr_1437_1438 k (by omega) h2
theorem cr_1438_1439 (k : ℕ) (h1 : 1438 ≤ k) (h2 : k < 1439) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1438 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1438_ok
theorem cr_1439_1440 (k : ℕ) (h1 : 1439 ≤ k) (h2 : k < 1440) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1439 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1439_ok
theorem cr_1440_1441 (k : ℕ) (h1 : 1440 ≤ k) (h2 : k < 1441) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1440 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1440_ok
theorem cr_1439_1441 (k : ℕ) (h1 : 1439 ≤ k) (h2 : k < 1441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1440 then cr_1439_1440 k h1 h else cr_1440_1441 k (by omega) h2
theorem cr_1438_1441 (k : ℕ) (h1 : 1438 ≤ k) (h2 : k < 1441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1439 then cr_1438_1439 k h1 h else cr_1439_1441 k (by omega) h2
theorem cr_1436_1441 (k : ℕ) (h1 : 1436 ≤ k) (h2 : k < 1441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1438 then cr_1436_1438 k h1 h else cr_1438_1441 k (by omega) h2
theorem cr_1441_1442 (k : ℕ) (h1 : 1441 ≤ k) (h2 : k < 1442) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1441 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1441_ok
theorem cr_1442_1443 (k : ℕ) (h1 : 1442 ≤ k) (h2 : k < 1443) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1442 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1442_ok
theorem cr_1441_1443 (k : ℕ) (h1 : 1441 ≤ k) (h2 : k < 1443) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1442 then cr_1441_1442 k h1 h else cr_1442_1443 k (by omega) h2
theorem cr_1443_1444 (k : ℕ) (h1 : 1443 ≤ k) (h2 : k < 1444) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1443 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1443_ok
theorem cr_1444_1445 (k : ℕ) (h1 : 1444 ≤ k) (h2 : k < 1445) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1444 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1444_ok
theorem cr_1445_1446 (k : ℕ) (h1 : 1445 ≤ k) (h2 : k < 1446) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1445 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1445_ok
theorem cr_1444_1446 (k : ℕ) (h1 : 1444 ≤ k) (h2 : k < 1446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1445 then cr_1444_1445 k h1 h else cr_1445_1446 k (by omega) h2
theorem cr_1443_1446 (k : ℕ) (h1 : 1443 ≤ k) (h2 : k < 1446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1444 then cr_1443_1444 k h1 h else cr_1444_1446 k (by omega) h2
theorem cr_1441_1446 (k : ℕ) (h1 : 1441 ≤ k) (h2 : k < 1446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1443 then cr_1441_1443 k h1 h else cr_1443_1446 k (by omega) h2
theorem cr_1436_1446 (k : ℕ) (h1 : 1436 ≤ k) (h2 : k < 1446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1441 then cr_1436_1441 k h1 h else cr_1441_1446 k (by omega) h2
theorem cr_1446_1447 (k : ℕ) (h1 : 1446 ≤ k) (h2 : k < 1447) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1446 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1446_ok
theorem cr_1447_1448 (k : ℕ) (h1 : 1447 ≤ k) (h2 : k < 1448) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1447 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1447_ok
theorem cr_1446_1448 (k : ℕ) (h1 : 1446 ≤ k) (h2 : k < 1448) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1447 then cr_1446_1447 k h1 h else cr_1447_1448 k (by omega) h2
theorem cr_1448_1449 (k : ℕ) (h1 : 1448 ≤ k) (h2 : k < 1449) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1448 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1448_ok
theorem cr_1449_1450 (k : ℕ) (h1 : 1449 ≤ k) (h2 : k < 1450) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1449 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1449_ok
theorem cr_1450_1451 (k : ℕ) (h1 : 1450 ≤ k) (h2 : k < 1451) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1450 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1450_ok
theorem cr_1449_1451 (k : ℕ) (h1 : 1449 ≤ k) (h2 : k < 1451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1450 then cr_1449_1450 k h1 h else cr_1450_1451 k (by omega) h2
theorem cr_1448_1451 (k : ℕ) (h1 : 1448 ≤ k) (h2 : k < 1451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1449 then cr_1448_1449 k h1 h else cr_1449_1451 k (by omega) h2
theorem cr_1446_1451 (k : ℕ) (h1 : 1446 ≤ k) (h2 : k < 1451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1448 then cr_1446_1448 k h1 h else cr_1448_1451 k (by omega) h2
theorem cr_1451_1452 (k : ℕ) (h1 : 1451 ≤ k) (h2 : k < 1452) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1451 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1451_ok
theorem cr_1452_1453 (k : ℕ) (h1 : 1452 ≤ k) (h2 : k < 1453) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1452 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1452_ok
theorem cr_1451_1453 (k : ℕ) (h1 : 1451 ≤ k) (h2 : k < 1453) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1452 then cr_1451_1452 k h1 h else cr_1452_1453 k (by omega) h2
theorem cr_1453_1454 (k : ℕ) (h1 : 1453 ≤ k) (h2 : k < 1454) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1453 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1453_ok
theorem cr_1454_1455 (k : ℕ) (h1 : 1454 ≤ k) (h2 : k < 1455) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1454 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1454_ok
theorem cr_1455_1456 (k : ℕ) (h1 : 1455 ≤ k) (h2 : k < 1456) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1455 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1455_ok
theorem cr_1454_1456 (k : ℕ) (h1 : 1454 ≤ k) (h2 : k < 1456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1455 then cr_1454_1455 k h1 h else cr_1455_1456 k (by omega) h2
theorem cr_1453_1456 (k : ℕ) (h1 : 1453 ≤ k) (h2 : k < 1456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1454 then cr_1453_1454 k h1 h else cr_1454_1456 k (by omega) h2
theorem cr_1451_1456 (k : ℕ) (h1 : 1451 ≤ k) (h2 : k < 1456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1453 then cr_1451_1453 k h1 h else cr_1453_1456 k (by omega) h2
theorem cr_1446_1456 (k : ℕ) (h1 : 1446 ≤ k) (h2 : k < 1456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1451 then cr_1446_1451 k h1 h else cr_1451_1456 k (by omega) h2
theorem cr_1436_1456 (k : ℕ) (h1 : 1436 ≤ k) (h2 : k < 1456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1446 then cr_1436_1446 k h1 h else cr_1446_1456 k (by omega) h2
theorem cr_1456_1457 (k : ℕ) (h1 : 1456 ≤ k) (h2 : k < 1457) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1456 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1456_ok
theorem cr_1457_1458 (k : ℕ) (h1 : 1457 ≤ k) (h2 : k < 1458) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1457 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1457_ok
theorem cr_1456_1458 (k : ℕ) (h1 : 1456 ≤ k) (h2 : k < 1458) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1457 then cr_1456_1457 k h1 h else cr_1457_1458 k (by omega) h2
theorem cr_1458_1459 (k : ℕ) (h1 : 1458 ≤ k) (h2 : k < 1459) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1458 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1458_ok
theorem cr_1459_1460 (k : ℕ) (h1 : 1459 ≤ k) (h2 : k < 1460) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1459 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1459_ok
theorem cr_1460_1461 (k : ℕ) (h1 : 1460 ≤ k) (h2 : k < 1461) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1460 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1460_ok
theorem cr_1459_1461 (k : ℕ) (h1 : 1459 ≤ k) (h2 : k < 1461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1460 then cr_1459_1460 k h1 h else cr_1460_1461 k (by omega) h2
theorem cr_1458_1461 (k : ℕ) (h1 : 1458 ≤ k) (h2 : k < 1461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1459 then cr_1458_1459 k h1 h else cr_1459_1461 k (by omega) h2
theorem cr_1456_1461 (k : ℕ) (h1 : 1456 ≤ k) (h2 : k < 1461) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1458 then cr_1456_1458 k h1 h else cr_1458_1461 k (by omega) h2
theorem cr_1461_1462 (k : ℕ) (h1 : 1461 ≤ k) (h2 : k < 1462) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1461 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1461_ok
theorem cr_1462_1463 (k : ℕ) (h1 : 1462 ≤ k) (h2 : k < 1463) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1462 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1462_ok
theorem cr_1461_1463 (k : ℕ) (h1 : 1461 ≤ k) (h2 : k < 1463) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1462 then cr_1461_1462 k h1 h else cr_1462_1463 k (by omega) h2
theorem cr_1463_1464 (k : ℕ) (h1 : 1463 ≤ k) (h2 : k < 1464) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1463 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1463_ok
theorem cr_1464_1465 (k : ℕ) (h1 : 1464 ≤ k) (h2 : k < 1465) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1464 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1464_ok
theorem cr_1465_1466 (k : ℕ) (h1 : 1465 ≤ k) (h2 : k < 1466) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1465 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1465_ok
theorem cr_1464_1466 (k : ℕ) (h1 : 1464 ≤ k) (h2 : k < 1466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1465 then cr_1464_1465 k h1 h else cr_1465_1466 k (by omega) h2
theorem cr_1463_1466 (k : ℕ) (h1 : 1463 ≤ k) (h2 : k < 1466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1464 then cr_1463_1464 k h1 h else cr_1464_1466 k (by omega) h2
theorem cr_1461_1466 (k : ℕ) (h1 : 1461 ≤ k) (h2 : k < 1466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1463 then cr_1461_1463 k h1 h else cr_1463_1466 k (by omega) h2
theorem cr_1456_1466 (k : ℕ) (h1 : 1456 ≤ k) (h2 : k < 1466) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1461 then cr_1456_1461 k h1 h else cr_1461_1466 k (by omega) h2
theorem cr_1466_1467 (k : ℕ) (h1 : 1466 ≤ k) (h2 : k < 1467) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1466 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1466_ok
theorem cr_1467_1468 (k : ℕ) (h1 : 1467 ≤ k) (h2 : k < 1468) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1467 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1467_ok
theorem cr_1466_1468 (k : ℕ) (h1 : 1466 ≤ k) (h2 : k < 1468) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1467 then cr_1466_1467 k h1 h else cr_1467_1468 k (by omega) h2
theorem cr_1468_1469 (k : ℕ) (h1 : 1468 ≤ k) (h2 : k < 1469) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1468 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1468_ok
theorem cr_1469_1470 (k : ℕ) (h1 : 1469 ≤ k) (h2 : k < 1470) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1469 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1469_ok
theorem cr_1470_1471 (k : ℕ) (h1 : 1470 ≤ k) (h2 : k < 1471) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1470 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1470_ok
theorem cr_1469_1471 (k : ℕ) (h1 : 1469 ≤ k) (h2 : k < 1471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1470 then cr_1469_1470 k h1 h else cr_1470_1471 k (by omega) h2
theorem cr_1468_1471 (k : ℕ) (h1 : 1468 ≤ k) (h2 : k < 1471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1469 then cr_1468_1469 k h1 h else cr_1469_1471 k (by omega) h2
theorem cr_1466_1471 (k : ℕ) (h1 : 1466 ≤ k) (h2 : k < 1471) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1468 then cr_1466_1468 k h1 h else cr_1468_1471 k (by omega) h2
theorem cr_1471_1472 (k : ℕ) (h1 : 1471 ≤ k) (h2 : k < 1472) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1471 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1471_ok
theorem cr_1472_1473 (k : ℕ) (h1 : 1472 ≤ k) (h2 : k < 1473) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1472 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1472_ok
theorem cr_1473_1474 (k : ℕ) (h1 : 1473 ≤ k) (h2 : k < 1474) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1473 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1473_ok
theorem cr_1472_1474 (k : ℕ) (h1 : 1472 ≤ k) (h2 : k < 1474) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1473 then cr_1472_1473 k h1 h else cr_1473_1474 k (by omega) h2
theorem cr_1471_1474 (k : ℕ) (h1 : 1471 ≤ k) (h2 : k < 1474) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1472 then cr_1471_1472 k h1 h else cr_1472_1474 k (by omega) h2
theorem cr_1474_1475 (k : ℕ) (h1 : 1474 ≤ k) (h2 : k < 1475) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1474 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1474_ok
theorem cr_1475_1476 (k : ℕ) (h1 : 1475 ≤ k) (h2 : k < 1476) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1475 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1475_ok
theorem cr_1476_1477 (k : ℕ) (h1 : 1476 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1476 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1476_ok
theorem cr_1475_1477 (k : ℕ) (h1 : 1475 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1476 then cr_1475_1476 k h1 h else cr_1476_1477 k (by omega) h2
theorem cr_1474_1477 (k : ℕ) (h1 : 1474 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1475 then cr_1474_1475 k h1 h else cr_1475_1477 k (by omega) h2
theorem cr_1471_1477 (k : ℕ) (h1 : 1471 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1474 then cr_1471_1474 k h1 h else cr_1474_1477 k (by omega) h2
theorem cr_1466_1477 (k : ℕ) (h1 : 1466 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1471 then cr_1466_1471 k h1 h else cr_1471_1477 k (by omega) h2
theorem cr_1456_1477 (k : ℕ) (h1 : 1456 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1466 then cr_1456_1466 k h1 h else cr_1466_1477 k (by omega) h2
theorem cr_1436_1477 (k : ℕ) (h1 : 1436 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1456 then cr_1436_1456 k h1 h else cr_1456_1477 k (by omega) h2
theorem cr_1395_1477 (k : ℕ) (h1 : 1395 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1436 then cr_1395_1436 k h1 h else cr_1436_1477 k (by omega) h2
theorem cr_1313_1477 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1395 then cr_1313_1395 k h1 h else cr_1395_1477 k (by omega) h2
theorem cr_1477_1478 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1478) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1477 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1477_ok
theorem cr_1478_1479 (k : ℕ) (h1 : 1478 ≤ k) (h2 : k < 1479) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1478 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1478_ok
theorem cr_1477_1479 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1479) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1478 then cr_1477_1478 k h1 h else cr_1478_1479 k (by omega) h2
theorem cr_1479_1480 (k : ℕ) (h1 : 1479 ≤ k) (h2 : k < 1480) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1479 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1479_ok
theorem cr_1480_1481 (k : ℕ) (h1 : 1480 ≤ k) (h2 : k < 1481) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1480 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1480_ok
theorem cr_1481_1482 (k : ℕ) (h1 : 1481 ≤ k) (h2 : k < 1482) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1481 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1481_ok
theorem cr_1480_1482 (k : ℕ) (h1 : 1480 ≤ k) (h2 : k < 1482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1481 then cr_1480_1481 k h1 h else cr_1481_1482 k (by omega) h2
theorem cr_1479_1482 (k : ℕ) (h1 : 1479 ≤ k) (h2 : k < 1482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1480 then cr_1479_1480 k h1 h else cr_1480_1482 k (by omega) h2
theorem cr_1477_1482 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1479 then cr_1477_1479 k h1 h else cr_1479_1482 k (by omega) h2
theorem cr_1482_1483 (k : ℕ) (h1 : 1482 ≤ k) (h2 : k < 1483) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1482 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1482_ok
theorem cr_1483_1484 (k : ℕ) (h1 : 1483 ≤ k) (h2 : k < 1484) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1483 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1483_ok
theorem cr_1482_1484 (k : ℕ) (h1 : 1482 ≤ k) (h2 : k < 1484) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1483 then cr_1482_1483 k h1 h else cr_1483_1484 k (by omega) h2
theorem cr_1484_1485 (k : ℕ) (h1 : 1484 ≤ k) (h2 : k < 1485) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1484 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1484_ok
theorem cr_1485_1486 (k : ℕ) (h1 : 1485 ≤ k) (h2 : k < 1486) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1485 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1485_ok
theorem cr_1486_1487 (k : ℕ) (h1 : 1486 ≤ k) (h2 : k < 1487) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1486 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1486_ok
theorem cr_1485_1487 (k : ℕ) (h1 : 1485 ≤ k) (h2 : k < 1487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1486 then cr_1485_1486 k h1 h else cr_1486_1487 k (by omega) h2
theorem cr_1484_1487 (k : ℕ) (h1 : 1484 ≤ k) (h2 : k < 1487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1485 then cr_1484_1485 k h1 h else cr_1485_1487 k (by omega) h2
theorem cr_1482_1487 (k : ℕ) (h1 : 1482 ≤ k) (h2 : k < 1487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1484 then cr_1482_1484 k h1 h else cr_1484_1487 k (by omega) h2
theorem cr_1477_1487 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1482 then cr_1477_1482 k h1 h else cr_1482_1487 k (by omega) h2
theorem cr_1487_1488 (k : ℕ) (h1 : 1487 ≤ k) (h2 : k < 1488) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1487 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1487_ok
theorem cr_1488_1489 (k : ℕ) (h1 : 1488 ≤ k) (h2 : k < 1489) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1488 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1488_ok
theorem cr_1487_1489 (k : ℕ) (h1 : 1487 ≤ k) (h2 : k < 1489) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1488 then cr_1487_1488 k h1 h else cr_1488_1489 k (by omega) h2
theorem cr_1489_1490 (k : ℕ) (h1 : 1489 ≤ k) (h2 : k < 1490) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1489 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1489_ok
theorem cr_1490_1491 (k : ℕ) (h1 : 1490 ≤ k) (h2 : k < 1491) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1490 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1490_ok
theorem cr_1491_1492 (k : ℕ) (h1 : 1491 ≤ k) (h2 : k < 1492) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1491 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1491_ok
theorem cr_1490_1492 (k : ℕ) (h1 : 1490 ≤ k) (h2 : k < 1492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1491 then cr_1490_1491 k h1 h else cr_1491_1492 k (by omega) h2
theorem cr_1489_1492 (k : ℕ) (h1 : 1489 ≤ k) (h2 : k < 1492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1490 then cr_1489_1490 k h1 h else cr_1490_1492 k (by omega) h2
theorem cr_1487_1492 (k : ℕ) (h1 : 1487 ≤ k) (h2 : k < 1492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1489 then cr_1487_1489 k h1 h else cr_1489_1492 k (by omega) h2
theorem cr_1492_1493 (k : ℕ) (h1 : 1492 ≤ k) (h2 : k < 1493) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1492 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1492_ok
theorem cr_1493_1494 (k : ℕ) (h1 : 1493 ≤ k) (h2 : k < 1494) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1493 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1493_ok
theorem cr_1492_1494 (k : ℕ) (h1 : 1492 ≤ k) (h2 : k < 1494) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1493 then cr_1492_1493 k h1 h else cr_1493_1494 k (by omega) h2
theorem cr_1494_1495 (k : ℕ) (h1 : 1494 ≤ k) (h2 : k < 1495) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1494 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1494_ok
theorem cr_1495_1496 (k : ℕ) (h1 : 1495 ≤ k) (h2 : k < 1496) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1495 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1495_ok
theorem cr_1496_1497 (k : ℕ) (h1 : 1496 ≤ k) (h2 : k < 1497) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1496 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1496_ok
theorem cr_1495_1497 (k : ℕ) (h1 : 1495 ≤ k) (h2 : k < 1497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1496 then cr_1495_1496 k h1 h else cr_1496_1497 k (by omega) h2
theorem cr_1494_1497 (k : ℕ) (h1 : 1494 ≤ k) (h2 : k < 1497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1495 then cr_1494_1495 k h1 h else cr_1495_1497 k (by omega) h2
theorem cr_1492_1497 (k : ℕ) (h1 : 1492 ≤ k) (h2 : k < 1497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1494 then cr_1492_1494 k h1 h else cr_1494_1497 k (by omega) h2
theorem cr_1487_1497 (k : ℕ) (h1 : 1487 ≤ k) (h2 : k < 1497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1492 then cr_1487_1492 k h1 h else cr_1492_1497 k (by omega) h2
theorem cr_1477_1497 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1487 then cr_1477_1487 k h1 h else cr_1487_1497 k (by omega) h2
theorem cr_1497_1498 (k : ℕ) (h1 : 1497 ≤ k) (h2 : k < 1498) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1497 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1497_ok
theorem cr_1498_1499 (k : ℕ) (h1 : 1498 ≤ k) (h2 : k < 1499) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1498 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1498_ok
theorem cr_1497_1499 (k : ℕ) (h1 : 1497 ≤ k) (h2 : k < 1499) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1498 then cr_1497_1498 k h1 h else cr_1498_1499 k (by omega) h2
theorem cr_1499_1500 (k : ℕ) (h1 : 1499 ≤ k) (h2 : k < 1500) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1499 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1499_ok
theorem cr_1500_1501 (k : ℕ) (h1 : 1500 ≤ k) (h2 : k < 1501) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1500 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1500_ok
theorem cr_1501_1502 (k : ℕ) (h1 : 1501 ≤ k) (h2 : k < 1502) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1501 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1501_ok
theorem cr_1500_1502 (k : ℕ) (h1 : 1500 ≤ k) (h2 : k < 1502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1501 then cr_1500_1501 k h1 h else cr_1501_1502 k (by omega) h2
theorem cr_1499_1502 (k : ℕ) (h1 : 1499 ≤ k) (h2 : k < 1502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1500 then cr_1499_1500 k h1 h else cr_1500_1502 k (by omega) h2
theorem cr_1497_1502 (k : ℕ) (h1 : 1497 ≤ k) (h2 : k < 1502) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1499 then cr_1497_1499 k h1 h else cr_1499_1502 k (by omega) h2
theorem cr_1502_1503 (k : ℕ) (h1 : 1502 ≤ k) (h2 : k < 1503) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1502 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1502_ok
theorem cr_1503_1504 (k : ℕ) (h1 : 1503 ≤ k) (h2 : k < 1504) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1503 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1503_ok
theorem cr_1502_1504 (k : ℕ) (h1 : 1502 ≤ k) (h2 : k < 1504) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1503 then cr_1502_1503 k h1 h else cr_1503_1504 k (by omega) h2
theorem cr_1504_1505 (k : ℕ) (h1 : 1504 ≤ k) (h2 : k < 1505) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1504 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1504_ok
theorem cr_1505_1506 (k : ℕ) (h1 : 1505 ≤ k) (h2 : k < 1506) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1505 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1505_ok
theorem cr_1506_1507 (k : ℕ) (h1 : 1506 ≤ k) (h2 : k < 1507) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1506 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1506_ok
theorem cr_1505_1507 (k : ℕ) (h1 : 1505 ≤ k) (h2 : k < 1507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1506 then cr_1505_1506 k h1 h else cr_1506_1507 k (by omega) h2
theorem cr_1504_1507 (k : ℕ) (h1 : 1504 ≤ k) (h2 : k < 1507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1505 then cr_1504_1505 k h1 h else cr_1505_1507 k (by omega) h2
theorem cr_1502_1507 (k : ℕ) (h1 : 1502 ≤ k) (h2 : k < 1507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1504 then cr_1502_1504 k h1 h else cr_1504_1507 k (by omega) h2
theorem cr_1497_1507 (k : ℕ) (h1 : 1497 ≤ k) (h2 : k < 1507) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1502 then cr_1497_1502 k h1 h else cr_1502_1507 k (by omega) h2
theorem cr_1507_1508 (k : ℕ) (h1 : 1507 ≤ k) (h2 : k < 1508) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1507 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1507_ok
theorem cr_1508_1509 (k : ℕ) (h1 : 1508 ≤ k) (h2 : k < 1509) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1508 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1508_ok
theorem cr_1507_1509 (k : ℕ) (h1 : 1507 ≤ k) (h2 : k < 1509) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1508 then cr_1507_1508 k h1 h else cr_1508_1509 k (by omega) h2
theorem cr_1509_1510 (k : ℕ) (h1 : 1509 ≤ k) (h2 : k < 1510) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1509 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1509_ok
theorem cr_1510_1511 (k : ℕ) (h1 : 1510 ≤ k) (h2 : k < 1511) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1510 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1510_ok
theorem cr_1511_1512 (k : ℕ) (h1 : 1511 ≤ k) (h2 : k < 1512) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1511 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1511_ok
theorem cr_1510_1512 (k : ℕ) (h1 : 1510 ≤ k) (h2 : k < 1512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1511 then cr_1510_1511 k h1 h else cr_1511_1512 k (by omega) h2
theorem cr_1509_1512 (k : ℕ) (h1 : 1509 ≤ k) (h2 : k < 1512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1510 then cr_1509_1510 k h1 h else cr_1510_1512 k (by omega) h2
theorem cr_1507_1512 (k : ℕ) (h1 : 1507 ≤ k) (h2 : k < 1512) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1509 then cr_1507_1509 k h1 h else cr_1509_1512 k (by omega) h2
theorem cr_1512_1513 (k : ℕ) (h1 : 1512 ≤ k) (h2 : k < 1513) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1512 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1512_ok
theorem cr_1513_1514 (k : ℕ) (h1 : 1513 ≤ k) (h2 : k < 1514) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1513 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1513_ok
theorem cr_1514_1515 (k : ℕ) (h1 : 1514 ≤ k) (h2 : k < 1515) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1514 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1514_ok
theorem cr_1513_1515 (k : ℕ) (h1 : 1513 ≤ k) (h2 : k < 1515) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1514 then cr_1513_1514 k h1 h else cr_1514_1515 k (by omega) h2
theorem cr_1512_1515 (k : ℕ) (h1 : 1512 ≤ k) (h2 : k < 1515) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1513 then cr_1512_1513 k h1 h else cr_1513_1515 k (by omega) h2
theorem cr_1515_1516 (k : ℕ) (h1 : 1515 ≤ k) (h2 : k < 1516) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1515 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1515_ok
theorem cr_1516_1517 (k : ℕ) (h1 : 1516 ≤ k) (h2 : k < 1517) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1516 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1516_ok
theorem cr_1517_1518 (k : ℕ) (h1 : 1517 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1517 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1517_ok
theorem cr_1516_1518 (k : ℕ) (h1 : 1516 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1517 then cr_1516_1517 k h1 h else cr_1517_1518 k (by omega) h2
theorem cr_1515_1518 (k : ℕ) (h1 : 1515 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1516 then cr_1515_1516 k h1 h else cr_1516_1518 k (by omega) h2
theorem cr_1512_1518 (k : ℕ) (h1 : 1512 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1515 then cr_1512_1515 k h1 h else cr_1515_1518 k (by omega) h2
theorem cr_1507_1518 (k : ℕ) (h1 : 1507 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1512 then cr_1507_1512 k h1 h else cr_1512_1518 k (by omega) h2
theorem cr_1497_1518 (k : ℕ) (h1 : 1497 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1507 then cr_1497_1507 k h1 h else cr_1507_1518 k (by omega) h2
theorem cr_1477_1518 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1497 then cr_1477_1497 k h1 h else cr_1497_1518 k (by omega) h2
theorem cr_1518_1519 (k : ℕ) (h1 : 1518 ≤ k) (h2 : k < 1519) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1518 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1518_ok
theorem cr_1519_1520 (k : ℕ) (h1 : 1519 ≤ k) (h2 : k < 1520) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1519 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1519_ok
theorem cr_1518_1520 (k : ℕ) (h1 : 1518 ≤ k) (h2 : k < 1520) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1519 then cr_1518_1519 k h1 h else cr_1519_1520 k (by omega) h2
theorem cr_1520_1521 (k : ℕ) (h1 : 1520 ≤ k) (h2 : k < 1521) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1520 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1520_ok
theorem cr_1521_1522 (k : ℕ) (h1 : 1521 ≤ k) (h2 : k < 1522) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1521 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1521_ok
theorem cr_1522_1523 (k : ℕ) (h1 : 1522 ≤ k) (h2 : k < 1523) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1522 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1522_ok
theorem cr_1521_1523 (k : ℕ) (h1 : 1521 ≤ k) (h2 : k < 1523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1522 then cr_1521_1522 k h1 h else cr_1522_1523 k (by omega) h2
theorem cr_1520_1523 (k : ℕ) (h1 : 1520 ≤ k) (h2 : k < 1523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1521 then cr_1520_1521 k h1 h else cr_1521_1523 k (by omega) h2
theorem cr_1518_1523 (k : ℕ) (h1 : 1518 ≤ k) (h2 : k < 1523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1520 then cr_1518_1520 k h1 h else cr_1520_1523 k (by omega) h2
theorem cr_1523_1524 (k : ℕ) (h1 : 1523 ≤ k) (h2 : k < 1524) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1523 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1523_ok
theorem cr_1524_1525 (k : ℕ) (h1 : 1524 ≤ k) (h2 : k < 1525) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1524 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1524_ok
theorem cr_1523_1525 (k : ℕ) (h1 : 1523 ≤ k) (h2 : k < 1525) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1524 then cr_1523_1524 k h1 h else cr_1524_1525 k (by omega) h2
theorem cr_1525_1526 (k : ℕ) (h1 : 1525 ≤ k) (h2 : k < 1526) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1525 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1525_ok
theorem cr_1526_1527 (k : ℕ) (h1 : 1526 ≤ k) (h2 : k < 1527) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1526 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1526_ok
theorem cr_1527_1528 (k : ℕ) (h1 : 1527 ≤ k) (h2 : k < 1528) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1527 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1527_ok
theorem cr_1526_1528 (k : ℕ) (h1 : 1526 ≤ k) (h2 : k < 1528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1527 then cr_1526_1527 k h1 h else cr_1527_1528 k (by omega) h2
theorem cr_1525_1528 (k : ℕ) (h1 : 1525 ≤ k) (h2 : k < 1528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1526 then cr_1525_1526 k h1 h else cr_1526_1528 k (by omega) h2
theorem cr_1523_1528 (k : ℕ) (h1 : 1523 ≤ k) (h2 : k < 1528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1525 then cr_1523_1525 k h1 h else cr_1525_1528 k (by omega) h2
theorem cr_1518_1528 (k : ℕ) (h1 : 1518 ≤ k) (h2 : k < 1528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1523 then cr_1518_1523 k h1 h else cr_1523_1528 k (by omega) h2
theorem cr_1528_1529 (k : ℕ) (h1 : 1528 ≤ k) (h2 : k < 1529) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1528 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1528_ok
theorem cr_1529_1530 (k : ℕ) (h1 : 1529 ≤ k) (h2 : k < 1530) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1529 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1529_ok
theorem cr_1528_1530 (k : ℕ) (h1 : 1528 ≤ k) (h2 : k < 1530) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1529 then cr_1528_1529 k h1 h else cr_1529_1530 k (by omega) h2
theorem cr_1530_1531 (k : ℕ) (h1 : 1530 ≤ k) (h2 : k < 1531) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1530 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1530_ok
theorem cr_1531_1532 (k : ℕ) (h1 : 1531 ≤ k) (h2 : k < 1532) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1531 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1531_ok
theorem cr_1532_1533 (k : ℕ) (h1 : 1532 ≤ k) (h2 : k < 1533) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1532 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1532_ok
theorem cr_1531_1533 (k : ℕ) (h1 : 1531 ≤ k) (h2 : k < 1533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1532 then cr_1531_1532 k h1 h else cr_1532_1533 k (by omega) h2
theorem cr_1530_1533 (k : ℕ) (h1 : 1530 ≤ k) (h2 : k < 1533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1531 then cr_1530_1531 k h1 h else cr_1531_1533 k (by omega) h2
theorem cr_1528_1533 (k : ℕ) (h1 : 1528 ≤ k) (h2 : k < 1533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1530 then cr_1528_1530 k h1 h else cr_1530_1533 k (by omega) h2
theorem cr_1533_1534 (k : ℕ) (h1 : 1533 ≤ k) (h2 : k < 1534) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1533 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1533_ok
theorem cr_1534_1535 (k : ℕ) (h1 : 1534 ≤ k) (h2 : k < 1535) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1534 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1534_ok
theorem cr_1533_1535 (k : ℕ) (h1 : 1533 ≤ k) (h2 : k < 1535) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1534 then cr_1533_1534 k h1 h else cr_1534_1535 k (by omega) h2
theorem cr_1535_1536 (k : ℕ) (h1 : 1535 ≤ k) (h2 : k < 1536) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1535 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1535_ok
theorem cr_1536_1537 (k : ℕ) (h1 : 1536 ≤ k) (h2 : k < 1537) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1536 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1536_ok
theorem cr_1537_1538 (k : ℕ) (h1 : 1537 ≤ k) (h2 : k < 1538) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1537 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1537_ok
theorem cr_1536_1538 (k : ℕ) (h1 : 1536 ≤ k) (h2 : k < 1538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1537 then cr_1536_1537 k h1 h else cr_1537_1538 k (by omega) h2
theorem cr_1535_1538 (k : ℕ) (h1 : 1535 ≤ k) (h2 : k < 1538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1536 then cr_1535_1536 k h1 h else cr_1536_1538 k (by omega) h2
theorem cr_1533_1538 (k : ℕ) (h1 : 1533 ≤ k) (h2 : k < 1538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1535 then cr_1533_1535 k h1 h else cr_1535_1538 k (by omega) h2
theorem cr_1528_1538 (k : ℕ) (h1 : 1528 ≤ k) (h2 : k < 1538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1533 then cr_1528_1533 k h1 h else cr_1533_1538 k (by omega) h2
theorem cr_1518_1538 (k : ℕ) (h1 : 1518 ≤ k) (h2 : k < 1538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1528 then cr_1518_1528 k h1 h else cr_1528_1538 k (by omega) h2
theorem cr_1538_1539 (k : ℕ) (h1 : 1538 ≤ k) (h2 : k < 1539) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1538 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1538_ok
theorem cr_1539_1540 (k : ℕ) (h1 : 1539 ≤ k) (h2 : k < 1540) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1539 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1539_ok
theorem cr_1538_1540 (k : ℕ) (h1 : 1538 ≤ k) (h2 : k < 1540) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1539 then cr_1538_1539 k h1 h else cr_1539_1540 k (by omega) h2
theorem cr_1540_1541 (k : ℕ) (h1 : 1540 ≤ k) (h2 : k < 1541) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1540 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1540_ok
theorem cr_1541_1542 (k : ℕ) (h1 : 1541 ≤ k) (h2 : k < 1542) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1541 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1541_ok
theorem cr_1542_1543 (k : ℕ) (h1 : 1542 ≤ k) (h2 : k < 1543) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1542 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1542_ok
theorem cr_1541_1543 (k : ℕ) (h1 : 1541 ≤ k) (h2 : k < 1543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1542 then cr_1541_1542 k h1 h else cr_1542_1543 k (by omega) h2
theorem cr_1540_1543 (k : ℕ) (h1 : 1540 ≤ k) (h2 : k < 1543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1541 then cr_1540_1541 k h1 h else cr_1541_1543 k (by omega) h2
theorem cr_1538_1543 (k : ℕ) (h1 : 1538 ≤ k) (h2 : k < 1543) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1540 then cr_1538_1540 k h1 h else cr_1540_1543 k (by omega) h2
theorem cr_1543_1544 (k : ℕ) (h1 : 1543 ≤ k) (h2 : k < 1544) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1543 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1543_ok
theorem cr_1544_1545 (k : ℕ) (h1 : 1544 ≤ k) (h2 : k < 1545) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1544 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1544_ok
theorem cr_1543_1545 (k : ℕ) (h1 : 1543 ≤ k) (h2 : k < 1545) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1544 then cr_1543_1544 k h1 h else cr_1544_1545 k (by omega) h2
theorem cr_1545_1546 (k : ℕ) (h1 : 1545 ≤ k) (h2 : k < 1546) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1545 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1545_ok
theorem cr_1546_1547 (k : ℕ) (h1 : 1546 ≤ k) (h2 : k < 1547) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1546 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1546_ok
theorem cr_1547_1548 (k : ℕ) (h1 : 1547 ≤ k) (h2 : k < 1548) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1547 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1547_ok
theorem cr_1546_1548 (k : ℕ) (h1 : 1546 ≤ k) (h2 : k < 1548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1547 then cr_1546_1547 k h1 h else cr_1547_1548 k (by omega) h2
theorem cr_1545_1548 (k : ℕ) (h1 : 1545 ≤ k) (h2 : k < 1548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1546 then cr_1545_1546 k h1 h else cr_1546_1548 k (by omega) h2
theorem cr_1543_1548 (k : ℕ) (h1 : 1543 ≤ k) (h2 : k < 1548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1545 then cr_1543_1545 k h1 h else cr_1545_1548 k (by omega) h2
theorem cr_1538_1548 (k : ℕ) (h1 : 1538 ≤ k) (h2 : k < 1548) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1543 then cr_1538_1543 k h1 h else cr_1543_1548 k (by omega) h2
theorem cr_1548_1549 (k : ℕ) (h1 : 1548 ≤ k) (h2 : k < 1549) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1548 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1548_ok
theorem cr_1549_1550 (k : ℕ) (h1 : 1549 ≤ k) (h2 : k < 1550) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1549 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1549_ok
theorem cr_1548_1550 (k : ℕ) (h1 : 1548 ≤ k) (h2 : k < 1550) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1549 then cr_1548_1549 k h1 h else cr_1549_1550 k (by omega) h2
theorem cr_1550_1551 (k : ℕ) (h1 : 1550 ≤ k) (h2 : k < 1551) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1550 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1550_ok
theorem cr_1551_1552 (k : ℕ) (h1 : 1551 ≤ k) (h2 : k < 1552) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1551 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1551_ok
theorem cr_1552_1553 (k : ℕ) (h1 : 1552 ≤ k) (h2 : k < 1553) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1552 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1552_ok
theorem cr_1551_1553 (k : ℕ) (h1 : 1551 ≤ k) (h2 : k < 1553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1552 then cr_1551_1552 k h1 h else cr_1552_1553 k (by omega) h2
theorem cr_1550_1553 (k : ℕ) (h1 : 1550 ≤ k) (h2 : k < 1553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1551 then cr_1550_1551 k h1 h else cr_1551_1553 k (by omega) h2
theorem cr_1548_1553 (k : ℕ) (h1 : 1548 ≤ k) (h2 : k < 1553) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1550 then cr_1548_1550 k h1 h else cr_1550_1553 k (by omega) h2
theorem cr_1553_1554 (k : ℕ) (h1 : 1553 ≤ k) (h2 : k < 1554) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1553 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1553_ok
theorem cr_1554_1555 (k : ℕ) (h1 : 1554 ≤ k) (h2 : k < 1555) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1554 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1554_ok
theorem cr_1555_1556 (k : ℕ) (h1 : 1555 ≤ k) (h2 : k < 1556) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1555 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1555_ok
theorem cr_1554_1556 (k : ℕ) (h1 : 1554 ≤ k) (h2 : k < 1556) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1555 then cr_1554_1555 k h1 h else cr_1555_1556 k (by omega) h2
theorem cr_1553_1556 (k : ℕ) (h1 : 1553 ≤ k) (h2 : k < 1556) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1554 then cr_1553_1554 k h1 h else cr_1554_1556 k (by omega) h2
theorem cr_1556_1557 (k : ℕ) (h1 : 1556 ≤ k) (h2 : k < 1557) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1556 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1556_ok
theorem cr_1557_1558 (k : ℕ) (h1 : 1557 ≤ k) (h2 : k < 1558) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1557 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1557_ok
theorem cr_1558_1559 (k : ℕ) (h1 : 1558 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1558 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1558_ok
theorem cr_1557_1559 (k : ℕ) (h1 : 1557 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1558 then cr_1557_1558 k h1 h else cr_1558_1559 k (by omega) h2
theorem cr_1556_1559 (k : ℕ) (h1 : 1556 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1557 then cr_1556_1557 k h1 h else cr_1557_1559 k (by omega) h2
theorem cr_1553_1559 (k : ℕ) (h1 : 1553 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1556 then cr_1553_1556 k h1 h else cr_1556_1559 k (by omega) h2
theorem cr_1548_1559 (k : ℕ) (h1 : 1548 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1553 then cr_1548_1553 k h1 h else cr_1553_1559 k (by omega) h2
theorem cr_1538_1559 (k : ℕ) (h1 : 1538 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1548 then cr_1538_1548 k h1 h else cr_1548_1559 k (by omega) h2
theorem cr_1518_1559 (k : ℕ) (h1 : 1518 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1538 then cr_1518_1538 k h1 h else cr_1538_1559 k (by omega) h2
theorem cr_1477_1559 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1518 then cr_1477_1518 k h1 h else cr_1518_1559 k (by omega) h2
theorem cr_1559_1560 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1560) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1559 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1559_ok
theorem cr_1560_1561 (k : ℕ) (h1 : 1560 ≤ k) (h2 : k < 1561) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1560 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1560_ok
theorem cr_1559_1561 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1561) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1560 then cr_1559_1560 k h1 h else cr_1560_1561 k (by omega) h2
theorem cr_1561_1562 (k : ℕ) (h1 : 1561 ≤ k) (h2 : k < 1562) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1561 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1561_ok
theorem cr_1562_1563 (k : ℕ) (h1 : 1562 ≤ k) (h2 : k < 1563) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1562 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1562_ok
theorem cr_1563_1564 (k : ℕ) (h1 : 1563 ≤ k) (h2 : k < 1564) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1563 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1563_ok
theorem cr_1562_1564 (k : ℕ) (h1 : 1562 ≤ k) (h2 : k < 1564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1563 then cr_1562_1563 k h1 h else cr_1563_1564 k (by omega) h2
theorem cr_1561_1564 (k : ℕ) (h1 : 1561 ≤ k) (h2 : k < 1564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1562 then cr_1561_1562 k h1 h else cr_1562_1564 k (by omega) h2
theorem cr_1559_1564 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1561 then cr_1559_1561 k h1 h else cr_1561_1564 k (by omega) h2
theorem cr_1564_1565 (k : ℕ) (h1 : 1564 ≤ k) (h2 : k < 1565) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1564 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1564_ok
theorem cr_1565_1566 (k : ℕ) (h1 : 1565 ≤ k) (h2 : k < 1566) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1565 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1565_ok
theorem cr_1564_1566 (k : ℕ) (h1 : 1564 ≤ k) (h2 : k < 1566) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1565 then cr_1564_1565 k h1 h else cr_1565_1566 k (by omega) h2
theorem cr_1566_1567 (k : ℕ) (h1 : 1566 ≤ k) (h2 : k < 1567) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1566 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1566_ok
theorem cr_1567_1568 (k : ℕ) (h1 : 1567 ≤ k) (h2 : k < 1568) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1567 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1567_ok
theorem cr_1568_1569 (k : ℕ) (h1 : 1568 ≤ k) (h2 : k < 1569) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1568 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1568_ok
theorem cr_1567_1569 (k : ℕ) (h1 : 1567 ≤ k) (h2 : k < 1569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1568 then cr_1567_1568 k h1 h else cr_1568_1569 k (by omega) h2
theorem cr_1566_1569 (k : ℕ) (h1 : 1566 ≤ k) (h2 : k < 1569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1567 then cr_1566_1567 k h1 h else cr_1567_1569 k (by omega) h2
theorem cr_1564_1569 (k : ℕ) (h1 : 1564 ≤ k) (h2 : k < 1569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1566 then cr_1564_1566 k h1 h else cr_1566_1569 k (by omega) h2
theorem cr_1559_1569 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1564 then cr_1559_1564 k h1 h else cr_1564_1569 k (by omega) h2
theorem cr_1569_1570 (k : ℕ) (h1 : 1569 ≤ k) (h2 : k < 1570) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1569 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1569_ok
theorem cr_1570_1571 (k : ℕ) (h1 : 1570 ≤ k) (h2 : k < 1571) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1570 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1570_ok
theorem cr_1569_1571 (k : ℕ) (h1 : 1569 ≤ k) (h2 : k < 1571) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1570 then cr_1569_1570 k h1 h else cr_1570_1571 k (by omega) h2
theorem cr_1571_1572 (k : ℕ) (h1 : 1571 ≤ k) (h2 : k < 1572) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1571 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1571_ok
theorem cr_1572_1573 (k : ℕ) (h1 : 1572 ≤ k) (h2 : k < 1573) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1572 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1572_ok
theorem cr_1573_1574 (k : ℕ) (h1 : 1573 ≤ k) (h2 : k < 1574) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1573 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1573_ok
theorem cr_1572_1574 (k : ℕ) (h1 : 1572 ≤ k) (h2 : k < 1574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1573 then cr_1572_1573 k h1 h else cr_1573_1574 k (by omega) h2
theorem cr_1571_1574 (k : ℕ) (h1 : 1571 ≤ k) (h2 : k < 1574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1572 then cr_1571_1572 k h1 h else cr_1572_1574 k (by omega) h2
theorem cr_1569_1574 (k : ℕ) (h1 : 1569 ≤ k) (h2 : k < 1574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1571 then cr_1569_1571 k h1 h else cr_1571_1574 k (by omega) h2
theorem cr_1574_1575 (k : ℕ) (h1 : 1574 ≤ k) (h2 : k < 1575) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1574 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1574_ok
theorem cr_1575_1576 (k : ℕ) (h1 : 1575 ≤ k) (h2 : k < 1576) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1575 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1575_ok
theorem cr_1574_1576 (k : ℕ) (h1 : 1574 ≤ k) (h2 : k < 1576) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1575 then cr_1574_1575 k h1 h else cr_1575_1576 k (by omega) h2
theorem cr_1576_1577 (k : ℕ) (h1 : 1576 ≤ k) (h2 : k < 1577) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1576 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1576_ok
theorem cr_1577_1578 (k : ℕ) (h1 : 1577 ≤ k) (h2 : k < 1578) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1577 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1577_ok
theorem cr_1578_1579 (k : ℕ) (h1 : 1578 ≤ k) (h2 : k < 1579) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1578 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1578_ok
theorem cr_1577_1579 (k : ℕ) (h1 : 1577 ≤ k) (h2 : k < 1579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1578 then cr_1577_1578 k h1 h else cr_1578_1579 k (by omega) h2
theorem cr_1576_1579 (k : ℕ) (h1 : 1576 ≤ k) (h2 : k < 1579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1577 then cr_1576_1577 k h1 h else cr_1577_1579 k (by omega) h2
theorem cr_1574_1579 (k : ℕ) (h1 : 1574 ≤ k) (h2 : k < 1579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1576 then cr_1574_1576 k h1 h else cr_1576_1579 k (by omega) h2
theorem cr_1569_1579 (k : ℕ) (h1 : 1569 ≤ k) (h2 : k < 1579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1574 then cr_1569_1574 k h1 h else cr_1574_1579 k (by omega) h2
theorem cr_1559_1579 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1569 then cr_1559_1569 k h1 h else cr_1569_1579 k (by omega) h2
theorem cr_1579_1580 (k : ℕ) (h1 : 1579 ≤ k) (h2 : k < 1580) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1579 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1579_ok
theorem cr_1580_1581 (k : ℕ) (h1 : 1580 ≤ k) (h2 : k < 1581) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1580 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1580_ok
theorem cr_1579_1581 (k : ℕ) (h1 : 1579 ≤ k) (h2 : k < 1581) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1580 then cr_1579_1580 k h1 h else cr_1580_1581 k (by omega) h2
theorem cr_1581_1582 (k : ℕ) (h1 : 1581 ≤ k) (h2 : k < 1582) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1581 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1581_ok
theorem cr_1582_1583 (k : ℕ) (h1 : 1582 ≤ k) (h2 : k < 1583) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1582 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1582_ok
theorem cr_1583_1584 (k : ℕ) (h1 : 1583 ≤ k) (h2 : k < 1584) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1583 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1583_ok
theorem cr_1582_1584 (k : ℕ) (h1 : 1582 ≤ k) (h2 : k < 1584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1583 then cr_1582_1583 k h1 h else cr_1583_1584 k (by omega) h2
theorem cr_1581_1584 (k : ℕ) (h1 : 1581 ≤ k) (h2 : k < 1584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1582 then cr_1581_1582 k h1 h else cr_1582_1584 k (by omega) h2
theorem cr_1579_1584 (k : ℕ) (h1 : 1579 ≤ k) (h2 : k < 1584) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1581 then cr_1579_1581 k h1 h else cr_1581_1584 k (by omega) h2
theorem cr_1584_1585 (k : ℕ) (h1 : 1584 ≤ k) (h2 : k < 1585) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1584 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1584_ok
theorem cr_1585_1586 (k : ℕ) (h1 : 1585 ≤ k) (h2 : k < 1586) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1585 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1585_ok
theorem cr_1584_1586 (k : ℕ) (h1 : 1584 ≤ k) (h2 : k < 1586) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1585 then cr_1584_1585 k h1 h else cr_1585_1586 k (by omega) h2
theorem cr_1586_1587 (k : ℕ) (h1 : 1586 ≤ k) (h2 : k < 1587) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1586 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1586_ok
theorem cr_1587_1588 (k : ℕ) (h1 : 1587 ≤ k) (h2 : k < 1588) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1587 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1587_ok
theorem cr_1588_1589 (k : ℕ) (h1 : 1588 ≤ k) (h2 : k < 1589) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1588 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1588_ok
theorem cr_1587_1589 (k : ℕ) (h1 : 1587 ≤ k) (h2 : k < 1589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1588 then cr_1587_1588 k h1 h else cr_1588_1589 k (by omega) h2
theorem cr_1586_1589 (k : ℕ) (h1 : 1586 ≤ k) (h2 : k < 1589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1587 then cr_1586_1587 k h1 h else cr_1587_1589 k (by omega) h2
theorem cr_1584_1589 (k : ℕ) (h1 : 1584 ≤ k) (h2 : k < 1589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1586 then cr_1584_1586 k h1 h else cr_1586_1589 k (by omega) h2
theorem cr_1579_1589 (k : ℕ) (h1 : 1579 ≤ k) (h2 : k < 1589) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1584 then cr_1579_1584 k h1 h else cr_1584_1589 k (by omega) h2
theorem cr_1589_1590 (k : ℕ) (h1 : 1589 ≤ k) (h2 : k < 1590) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1589 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1589_ok
theorem cr_1590_1591 (k : ℕ) (h1 : 1590 ≤ k) (h2 : k < 1591) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1590 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1590_ok
theorem cr_1589_1591 (k : ℕ) (h1 : 1589 ≤ k) (h2 : k < 1591) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1590 then cr_1589_1590 k h1 h else cr_1590_1591 k (by omega) h2
theorem cr_1591_1592 (k : ℕ) (h1 : 1591 ≤ k) (h2 : k < 1592) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1591 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1591_ok
theorem cr_1592_1593 (k : ℕ) (h1 : 1592 ≤ k) (h2 : k < 1593) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1592 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1592_ok
theorem cr_1593_1594 (k : ℕ) (h1 : 1593 ≤ k) (h2 : k < 1594) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1593 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1593_ok
theorem cr_1592_1594 (k : ℕ) (h1 : 1592 ≤ k) (h2 : k < 1594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1593 then cr_1592_1593 k h1 h else cr_1593_1594 k (by omega) h2
theorem cr_1591_1594 (k : ℕ) (h1 : 1591 ≤ k) (h2 : k < 1594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1592 then cr_1591_1592 k h1 h else cr_1592_1594 k (by omega) h2
theorem cr_1589_1594 (k : ℕ) (h1 : 1589 ≤ k) (h2 : k < 1594) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1591 then cr_1589_1591 k h1 h else cr_1591_1594 k (by omega) h2
theorem cr_1594_1595 (k : ℕ) (h1 : 1594 ≤ k) (h2 : k < 1595) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1594 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1594_ok
theorem cr_1595_1596 (k : ℕ) (h1 : 1595 ≤ k) (h2 : k < 1596) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1595 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1595_ok
theorem cr_1596_1597 (k : ℕ) (h1 : 1596 ≤ k) (h2 : k < 1597) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1596 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1596_ok
theorem cr_1595_1597 (k : ℕ) (h1 : 1595 ≤ k) (h2 : k < 1597) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1596 then cr_1595_1596 k h1 h else cr_1596_1597 k (by omega) h2
theorem cr_1594_1597 (k : ℕ) (h1 : 1594 ≤ k) (h2 : k < 1597) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1595 then cr_1594_1595 k h1 h else cr_1595_1597 k (by omega) h2
theorem cr_1597_1598 (k : ℕ) (h1 : 1597 ≤ k) (h2 : k < 1598) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1597 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1597_ok
theorem cr_1598_1599 (k : ℕ) (h1 : 1598 ≤ k) (h2 : k < 1599) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1598 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1598_ok
theorem cr_1599_1600 (k : ℕ) (h1 : 1599 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1599 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1599_ok
theorem cr_1598_1600 (k : ℕ) (h1 : 1598 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1599 then cr_1598_1599 k h1 h else cr_1599_1600 k (by omega) h2
theorem cr_1597_1600 (k : ℕ) (h1 : 1597 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1598 then cr_1597_1598 k h1 h else cr_1598_1600 k (by omega) h2
theorem cr_1594_1600 (k : ℕ) (h1 : 1594 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1597 then cr_1594_1597 k h1 h else cr_1597_1600 k (by omega) h2
theorem cr_1589_1600 (k : ℕ) (h1 : 1589 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1594 then cr_1589_1594 k h1 h else cr_1594_1600 k (by omega) h2
theorem cr_1579_1600 (k : ℕ) (h1 : 1579 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1589 then cr_1579_1589 k h1 h else cr_1589_1600 k (by omega) h2
theorem cr_1559_1600 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1579 then cr_1559_1579 k h1 h else cr_1579_1600 k (by omega) h2
theorem cr_1600_1601 (k : ℕ) (h1 : 1600 ≤ k) (h2 : k < 1601) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1600 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1600_ok
theorem cr_1601_1602 (k : ℕ) (h1 : 1601 ≤ k) (h2 : k < 1602) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1601 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1601_ok
theorem cr_1600_1602 (k : ℕ) (h1 : 1600 ≤ k) (h2 : k < 1602) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1601 then cr_1600_1601 k h1 h else cr_1601_1602 k (by omega) h2
theorem cr_1602_1603 (k : ℕ) (h1 : 1602 ≤ k) (h2 : k < 1603) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1602 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1602_ok
theorem cr_1603_1604 (k : ℕ) (h1 : 1603 ≤ k) (h2 : k < 1604) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1603 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1603_ok
theorem cr_1604_1605 (k : ℕ) (h1 : 1604 ≤ k) (h2 : k < 1605) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1604 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1604_ok
theorem cr_1603_1605 (k : ℕ) (h1 : 1603 ≤ k) (h2 : k < 1605) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1604 then cr_1603_1604 k h1 h else cr_1604_1605 k (by omega) h2
theorem cr_1602_1605 (k : ℕ) (h1 : 1602 ≤ k) (h2 : k < 1605) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1603 then cr_1602_1603 k h1 h else cr_1603_1605 k (by omega) h2
theorem cr_1600_1605 (k : ℕ) (h1 : 1600 ≤ k) (h2 : k < 1605) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1602 then cr_1600_1602 k h1 h else cr_1602_1605 k (by omega) h2
theorem cr_1605_1606 (k : ℕ) (h1 : 1605 ≤ k) (h2 : k < 1606) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1605 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1605_ok
theorem cr_1606_1607 (k : ℕ) (h1 : 1606 ≤ k) (h2 : k < 1607) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1606 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1606_ok
theorem cr_1605_1607 (k : ℕ) (h1 : 1605 ≤ k) (h2 : k < 1607) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1606 then cr_1605_1606 k h1 h else cr_1606_1607 k (by omega) h2
theorem cr_1607_1608 (k : ℕ) (h1 : 1607 ≤ k) (h2 : k < 1608) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1607 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1607_ok
theorem cr_1608_1609 (k : ℕ) (h1 : 1608 ≤ k) (h2 : k < 1609) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1608 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1608_ok
theorem cr_1609_1610 (k : ℕ) (h1 : 1609 ≤ k) (h2 : k < 1610) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1609 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1609_ok
theorem cr_1608_1610 (k : ℕ) (h1 : 1608 ≤ k) (h2 : k < 1610) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1609 then cr_1608_1609 k h1 h else cr_1609_1610 k (by omega) h2
theorem cr_1607_1610 (k : ℕ) (h1 : 1607 ≤ k) (h2 : k < 1610) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1608 then cr_1607_1608 k h1 h else cr_1608_1610 k (by omega) h2
theorem cr_1605_1610 (k : ℕ) (h1 : 1605 ≤ k) (h2 : k < 1610) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1607 then cr_1605_1607 k h1 h else cr_1607_1610 k (by omega) h2
theorem cr_1600_1610 (k : ℕ) (h1 : 1600 ≤ k) (h2 : k < 1610) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1605 then cr_1600_1605 k h1 h else cr_1605_1610 k (by omega) h2
theorem cr_1610_1611 (k : ℕ) (h1 : 1610 ≤ k) (h2 : k < 1611) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1610 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1610_ok
theorem cr_1611_1612 (k : ℕ) (h1 : 1611 ≤ k) (h2 : k < 1612) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1611 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1611_ok
theorem cr_1610_1612 (k : ℕ) (h1 : 1610 ≤ k) (h2 : k < 1612) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1611 then cr_1610_1611 k h1 h else cr_1611_1612 k (by omega) h2
theorem cr_1612_1613 (k : ℕ) (h1 : 1612 ≤ k) (h2 : k < 1613) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1612 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1612_ok
theorem cr_1613_1614 (k : ℕ) (h1 : 1613 ≤ k) (h2 : k < 1614) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1613 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1613_ok
theorem cr_1614_1615 (k : ℕ) (h1 : 1614 ≤ k) (h2 : k < 1615) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1614 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1614_ok
theorem cr_1613_1615 (k : ℕ) (h1 : 1613 ≤ k) (h2 : k < 1615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1614 then cr_1613_1614 k h1 h else cr_1614_1615 k (by omega) h2
theorem cr_1612_1615 (k : ℕ) (h1 : 1612 ≤ k) (h2 : k < 1615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1613 then cr_1612_1613 k h1 h else cr_1613_1615 k (by omega) h2
theorem cr_1610_1615 (k : ℕ) (h1 : 1610 ≤ k) (h2 : k < 1615) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1612 then cr_1610_1612 k h1 h else cr_1612_1615 k (by omega) h2
theorem cr_1615_1616 (k : ℕ) (h1 : 1615 ≤ k) (h2 : k < 1616) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1615 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1615_ok
theorem cr_1616_1617 (k : ℕ) (h1 : 1616 ≤ k) (h2 : k < 1617) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1616 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1616_ok
theorem cr_1615_1617 (k : ℕ) (h1 : 1615 ≤ k) (h2 : k < 1617) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1616 then cr_1615_1616 k h1 h else cr_1616_1617 k (by omega) h2
theorem cr_1617_1618 (k : ℕ) (h1 : 1617 ≤ k) (h2 : k < 1618) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1617 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1617_ok
theorem cr_1618_1619 (k : ℕ) (h1 : 1618 ≤ k) (h2 : k < 1619) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1618 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1618_ok
theorem cr_1619_1620 (k : ℕ) (h1 : 1619 ≤ k) (h2 : k < 1620) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1619 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1619_ok
theorem cr_1618_1620 (k : ℕ) (h1 : 1618 ≤ k) (h2 : k < 1620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1619 then cr_1618_1619 k h1 h else cr_1619_1620 k (by omega) h2
theorem cr_1617_1620 (k : ℕ) (h1 : 1617 ≤ k) (h2 : k < 1620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1618 then cr_1617_1618 k h1 h else cr_1618_1620 k (by omega) h2
theorem cr_1615_1620 (k : ℕ) (h1 : 1615 ≤ k) (h2 : k < 1620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1617 then cr_1615_1617 k h1 h else cr_1617_1620 k (by omega) h2
theorem cr_1610_1620 (k : ℕ) (h1 : 1610 ≤ k) (h2 : k < 1620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1615 then cr_1610_1615 k h1 h else cr_1615_1620 k (by omega) h2
theorem cr_1600_1620 (k : ℕ) (h1 : 1600 ≤ k) (h2 : k < 1620) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1610 then cr_1600_1610 k h1 h else cr_1610_1620 k (by omega) h2
theorem cr_1620_1621 (k : ℕ) (h1 : 1620 ≤ k) (h2 : k < 1621) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1620 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1620_ok
theorem cr_1621_1622 (k : ℕ) (h1 : 1621 ≤ k) (h2 : k < 1622) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1621 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1621_ok
theorem cr_1620_1622 (k : ℕ) (h1 : 1620 ≤ k) (h2 : k < 1622) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1621 then cr_1620_1621 k h1 h else cr_1621_1622 k (by omega) h2
theorem cr_1622_1623 (k : ℕ) (h1 : 1622 ≤ k) (h2 : k < 1623) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1622 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1622_ok
theorem cr_1623_1624 (k : ℕ) (h1 : 1623 ≤ k) (h2 : k < 1624) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1623 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1623_ok
theorem cr_1624_1625 (k : ℕ) (h1 : 1624 ≤ k) (h2 : k < 1625) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1624 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1624_ok
theorem cr_1623_1625 (k : ℕ) (h1 : 1623 ≤ k) (h2 : k < 1625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1624 then cr_1623_1624 k h1 h else cr_1624_1625 k (by omega) h2
theorem cr_1622_1625 (k : ℕ) (h1 : 1622 ≤ k) (h2 : k < 1625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1623 then cr_1622_1623 k h1 h else cr_1623_1625 k (by omega) h2
theorem cr_1620_1625 (k : ℕ) (h1 : 1620 ≤ k) (h2 : k < 1625) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1622 then cr_1620_1622 k h1 h else cr_1622_1625 k (by omega) h2
theorem cr_1625_1626 (k : ℕ) (h1 : 1625 ≤ k) (h2 : k < 1626) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1625 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1625_ok
theorem cr_1626_1627 (k : ℕ) (h1 : 1626 ≤ k) (h2 : k < 1627) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1626 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1626_ok
theorem cr_1625_1627 (k : ℕ) (h1 : 1625 ≤ k) (h2 : k < 1627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1626 then cr_1625_1626 k h1 h else cr_1626_1627 k (by omega) h2
theorem cr_1627_1628 (k : ℕ) (h1 : 1627 ≤ k) (h2 : k < 1628) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1627 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1627_ok
theorem cr_1628_1629 (k : ℕ) (h1 : 1628 ≤ k) (h2 : k < 1629) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1628 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1628_ok
theorem cr_1629_1630 (k : ℕ) (h1 : 1629 ≤ k) (h2 : k < 1630) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1629 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1629_ok
theorem cr_1628_1630 (k : ℕ) (h1 : 1628 ≤ k) (h2 : k < 1630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1629 then cr_1628_1629 k h1 h else cr_1629_1630 k (by omega) h2
theorem cr_1627_1630 (k : ℕ) (h1 : 1627 ≤ k) (h2 : k < 1630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1628 then cr_1627_1628 k h1 h else cr_1628_1630 k (by omega) h2
theorem cr_1625_1630 (k : ℕ) (h1 : 1625 ≤ k) (h2 : k < 1630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1627 then cr_1625_1627 k h1 h else cr_1627_1630 k (by omega) h2
theorem cr_1620_1630 (k : ℕ) (h1 : 1620 ≤ k) (h2 : k < 1630) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1625 then cr_1620_1625 k h1 h else cr_1625_1630 k (by omega) h2
theorem cr_1630_1631 (k : ℕ) (h1 : 1630 ≤ k) (h2 : k < 1631) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1630 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1630_ok
theorem cr_1631_1632 (k : ℕ) (h1 : 1631 ≤ k) (h2 : k < 1632) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1631 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1631_ok
theorem cr_1630_1632 (k : ℕ) (h1 : 1630 ≤ k) (h2 : k < 1632) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1631 then cr_1630_1631 k h1 h else cr_1631_1632 k (by omega) h2
theorem cr_1632_1633 (k : ℕ) (h1 : 1632 ≤ k) (h2 : k < 1633) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1632 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1632_ok
theorem cr_1633_1634 (k : ℕ) (h1 : 1633 ≤ k) (h2 : k < 1634) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1633 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1633_ok
theorem cr_1634_1635 (k : ℕ) (h1 : 1634 ≤ k) (h2 : k < 1635) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1634 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1634_ok
theorem cr_1633_1635 (k : ℕ) (h1 : 1633 ≤ k) (h2 : k < 1635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1634 then cr_1633_1634 k h1 h else cr_1634_1635 k (by omega) h2
theorem cr_1632_1635 (k : ℕ) (h1 : 1632 ≤ k) (h2 : k < 1635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1633 then cr_1632_1633 k h1 h else cr_1633_1635 k (by omega) h2
theorem cr_1630_1635 (k : ℕ) (h1 : 1630 ≤ k) (h2 : k < 1635) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1632 then cr_1630_1632 k h1 h else cr_1632_1635 k (by omega) h2
theorem cr_1635_1636 (k : ℕ) (h1 : 1635 ≤ k) (h2 : k < 1636) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1635 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1635_ok
theorem cr_1636_1637 (k : ℕ) (h1 : 1636 ≤ k) (h2 : k < 1637) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1636 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1636_ok
theorem cr_1637_1638 (k : ℕ) (h1 : 1637 ≤ k) (h2 : k < 1638) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1637 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1637_ok
theorem cr_1636_1638 (k : ℕ) (h1 : 1636 ≤ k) (h2 : k < 1638) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1637 then cr_1636_1637 k h1 h else cr_1637_1638 k (by omega) h2
theorem cr_1635_1638 (k : ℕ) (h1 : 1635 ≤ k) (h2 : k < 1638) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1636 then cr_1635_1636 k h1 h else cr_1636_1638 k (by omega) h2
theorem cr_1638_1639 (k : ℕ) (h1 : 1638 ≤ k) (h2 : k < 1639) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1638 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1638_ok
theorem cr_1639_1640 (k : ℕ) (h1 : 1639 ≤ k) (h2 : k < 1640) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1639 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1639_ok
theorem cr_1640_1641 (k : ℕ) (h1 : 1640 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1640 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1640_ok
theorem cr_1639_1641 (k : ℕ) (h1 : 1639 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1640 then cr_1639_1640 k h1 h else cr_1640_1641 k (by omega) h2
theorem cr_1638_1641 (k : ℕ) (h1 : 1638 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1639 then cr_1638_1639 k h1 h else cr_1639_1641 k (by omega) h2
theorem cr_1635_1641 (k : ℕ) (h1 : 1635 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1638 then cr_1635_1638 k h1 h else cr_1638_1641 k (by omega) h2
theorem cr_1630_1641 (k : ℕ) (h1 : 1630 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1635 then cr_1630_1635 k h1 h else cr_1635_1641 k (by omega) h2
theorem cr_1620_1641 (k : ℕ) (h1 : 1620 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1630 then cr_1620_1630 k h1 h else cr_1630_1641 k (by omega) h2
theorem cr_1600_1641 (k : ℕ) (h1 : 1600 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1620 then cr_1600_1620 k h1 h else cr_1620_1641 k (by omega) h2
theorem cr_1559_1641 (k : ℕ) (h1 : 1559 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1600 then cr_1559_1600 k h1 h else cr_1600_1641 k (by omega) h2
theorem cr_1477_1641 (k : ℕ) (h1 : 1477 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1559 then cr_1477_1559 k h1 h else cr_1559_1641 k (by omega) h2
theorem cr_1313_1641 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1641) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1477 then cr_1313_1477 k h1 h else cr_1477_1641 k (by omega) h2
theorem cr_1641_1642 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1642) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1641 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1641_ok
theorem cr_1642_1643 (k : ℕ) (h1 : 1642 ≤ k) (h2 : k < 1643) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1642 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1642_ok
theorem cr_1641_1643 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1643) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1642 then cr_1641_1642 k h1 h else cr_1642_1643 k (by omega) h2
theorem cr_1643_1644 (k : ℕ) (h1 : 1643 ≤ k) (h2 : k < 1644) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1643 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1643_ok
theorem cr_1644_1645 (k : ℕ) (h1 : 1644 ≤ k) (h2 : k < 1645) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1644 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1644_ok
theorem cr_1645_1646 (k : ℕ) (h1 : 1645 ≤ k) (h2 : k < 1646) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1645 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1645_ok
theorem cr_1644_1646 (k : ℕ) (h1 : 1644 ≤ k) (h2 : k < 1646) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1645 then cr_1644_1645 k h1 h else cr_1645_1646 k (by omega) h2
theorem cr_1643_1646 (k : ℕ) (h1 : 1643 ≤ k) (h2 : k < 1646) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1644 then cr_1643_1644 k h1 h else cr_1644_1646 k (by omega) h2
theorem cr_1641_1646 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1646) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1643 then cr_1641_1643 k h1 h else cr_1643_1646 k (by omega) h2
theorem cr_1646_1647 (k : ℕ) (h1 : 1646 ≤ k) (h2 : k < 1647) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1646 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1646_ok
theorem cr_1647_1648 (k : ℕ) (h1 : 1647 ≤ k) (h2 : k < 1648) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1647 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1647_ok
theorem cr_1646_1648 (k : ℕ) (h1 : 1646 ≤ k) (h2 : k < 1648) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1647 then cr_1646_1647 k h1 h else cr_1647_1648 k (by omega) h2
theorem cr_1648_1649 (k : ℕ) (h1 : 1648 ≤ k) (h2 : k < 1649) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1648 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1648_ok
theorem cr_1649_1650 (k : ℕ) (h1 : 1649 ≤ k) (h2 : k < 1650) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1649 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1649_ok
theorem cr_1650_1651 (k : ℕ) (h1 : 1650 ≤ k) (h2 : k < 1651) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1650 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1650_ok
theorem cr_1649_1651 (k : ℕ) (h1 : 1649 ≤ k) (h2 : k < 1651) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1650 then cr_1649_1650 k h1 h else cr_1650_1651 k (by omega) h2
theorem cr_1648_1651 (k : ℕ) (h1 : 1648 ≤ k) (h2 : k < 1651) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1649 then cr_1648_1649 k h1 h else cr_1649_1651 k (by omega) h2
theorem cr_1646_1651 (k : ℕ) (h1 : 1646 ≤ k) (h2 : k < 1651) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1648 then cr_1646_1648 k h1 h else cr_1648_1651 k (by omega) h2
theorem cr_1641_1651 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1651) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1646 then cr_1641_1646 k h1 h else cr_1646_1651 k (by omega) h2
theorem cr_1651_1652 (k : ℕ) (h1 : 1651 ≤ k) (h2 : k < 1652) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1651 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1651_ok
theorem cr_1652_1653 (k : ℕ) (h1 : 1652 ≤ k) (h2 : k < 1653) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1652 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1652_ok
theorem cr_1651_1653 (k : ℕ) (h1 : 1651 ≤ k) (h2 : k < 1653) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1652 then cr_1651_1652 k h1 h else cr_1652_1653 k (by omega) h2
theorem cr_1653_1654 (k : ℕ) (h1 : 1653 ≤ k) (h2 : k < 1654) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1653 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1653_ok
theorem cr_1654_1655 (k : ℕ) (h1 : 1654 ≤ k) (h2 : k < 1655) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1654 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1654_ok
theorem cr_1655_1656 (k : ℕ) (h1 : 1655 ≤ k) (h2 : k < 1656) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1655 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1655_ok
theorem cr_1654_1656 (k : ℕ) (h1 : 1654 ≤ k) (h2 : k < 1656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1655 then cr_1654_1655 k h1 h else cr_1655_1656 k (by omega) h2
theorem cr_1653_1656 (k : ℕ) (h1 : 1653 ≤ k) (h2 : k < 1656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1654 then cr_1653_1654 k h1 h else cr_1654_1656 k (by omega) h2
theorem cr_1651_1656 (k : ℕ) (h1 : 1651 ≤ k) (h2 : k < 1656) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1653 then cr_1651_1653 k h1 h else cr_1653_1656 k (by omega) h2
theorem cr_1656_1657 (k : ℕ) (h1 : 1656 ≤ k) (h2 : k < 1657) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1656 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1656_ok
theorem cr_1657_1658 (k : ℕ) (h1 : 1657 ≤ k) (h2 : k < 1658) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1657 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1657_ok
theorem cr_1656_1658 (k : ℕ) (h1 : 1656 ≤ k) (h2 : k < 1658) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1657 then cr_1656_1657 k h1 h else cr_1657_1658 k (by omega) h2
theorem cr_1658_1659 (k : ℕ) (h1 : 1658 ≤ k) (h2 : k < 1659) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1658 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1658_ok
theorem cr_1659_1660 (k : ℕ) (h1 : 1659 ≤ k) (h2 : k < 1660) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1659 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1659_ok
theorem cr_1660_1661 (k : ℕ) (h1 : 1660 ≤ k) (h2 : k < 1661) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1660 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1660_ok
theorem cr_1659_1661 (k : ℕ) (h1 : 1659 ≤ k) (h2 : k < 1661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1660 then cr_1659_1660 k h1 h else cr_1660_1661 k (by omega) h2
theorem cr_1658_1661 (k : ℕ) (h1 : 1658 ≤ k) (h2 : k < 1661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1659 then cr_1658_1659 k h1 h else cr_1659_1661 k (by omega) h2
theorem cr_1656_1661 (k : ℕ) (h1 : 1656 ≤ k) (h2 : k < 1661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1658 then cr_1656_1658 k h1 h else cr_1658_1661 k (by omega) h2
theorem cr_1651_1661 (k : ℕ) (h1 : 1651 ≤ k) (h2 : k < 1661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1656 then cr_1651_1656 k h1 h else cr_1656_1661 k (by omega) h2
theorem cr_1641_1661 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1661) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1651 then cr_1641_1651 k h1 h else cr_1651_1661 k (by omega) h2
theorem cr_1661_1662 (k : ℕ) (h1 : 1661 ≤ k) (h2 : k < 1662) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1661 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1661_ok
theorem cr_1662_1663 (k : ℕ) (h1 : 1662 ≤ k) (h2 : k < 1663) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1662 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1662_ok
theorem cr_1661_1663 (k : ℕ) (h1 : 1661 ≤ k) (h2 : k < 1663) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1662 then cr_1661_1662 k h1 h else cr_1662_1663 k (by omega) h2
theorem cr_1663_1664 (k : ℕ) (h1 : 1663 ≤ k) (h2 : k < 1664) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1663 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1663_ok
theorem cr_1664_1665 (k : ℕ) (h1 : 1664 ≤ k) (h2 : k < 1665) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1664 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1664_ok
theorem cr_1665_1666 (k : ℕ) (h1 : 1665 ≤ k) (h2 : k < 1666) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1665 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1665_ok
theorem cr_1664_1666 (k : ℕ) (h1 : 1664 ≤ k) (h2 : k < 1666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1665 then cr_1664_1665 k h1 h else cr_1665_1666 k (by omega) h2
theorem cr_1663_1666 (k : ℕ) (h1 : 1663 ≤ k) (h2 : k < 1666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1664 then cr_1663_1664 k h1 h else cr_1664_1666 k (by omega) h2
theorem cr_1661_1666 (k : ℕ) (h1 : 1661 ≤ k) (h2 : k < 1666) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1663 then cr_1661_1663 k h1 h else cr_1663_1666 k (by omega) h2
theorem cr_1666_1667 (k : ℕ) (h1 : 1666 ≤ k) (h2 : k < 1667) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1666 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1666_ok
theorem cr_1667_1668 (k : ℕ) (h1 : 1667 ≤ k) (h2 : k < 1668) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1667 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1667_ok
theorem cr_1666_1668 (k : ℕ) (h1 : 1666 ≤ k) (h2 : k < 1668) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1667 then cr_1666_1667 k h1 h else cr_1667_1668 k (by omega) h2
theorem cr_1668_1669 (k : ℕ) (h1 : 1668 ≤ k) (h2 : k < 1669) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1668 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1668_ok
theorem cr_1669_1670 (k : ℕ) (h1 : 1669 ≤ k) (h2 : k < 1670) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1669 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1669_ok
theorem cr_1670_1671 (k : ℕ) (h1 : 1670 ≤ k) (h2 : k < 1671) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1670 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1670_ok
theorem cr_1669_1671 (k : ℕ) (h1 : 1669 ≤ k) (h2 : k < 1671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1670 then cr_1669_1670 k h1 h else cr_1670_1671 k (by omega) h2
theorem cr_1668_1671 (k : ℕ) (h1 : 1668 ≤ k) (h2 : k < 1671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1669 then cr_1668_1669 k h1 h else cr_1669_1671 k (by omega) h2
theorem cr_1666_1671 (k : ℕ) (h1 : 1666 ≤ k) (h2 : k < 1671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1668 then cr_1666_1668 k h1 h else cr_1668_1671 k (by omega) h2
theorem cr_1661_1671 (k : ℕ) (h1 : 1661 ≤ k) (h2 : k < 1671) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1666 then cr_1661_1666 k h1 h else cr_1666_1671 k (by omega) h2
theorem cr_1671_1672 (k : ℕ) (h1 : 1671 ≤ k) (h2 : k < 1672) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1671 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1671_ok
theorem cr_1672_1673 (k : ℕ) (h1 : 1672 ≤ k) (h2 : k < 1673) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1672 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1672_ok
theorem cr_1671_1673 (k : ℕ) (h1 : 1671 ≤ k) (h2 : k < 1673) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1672 then cr_1671_1672 k h1 h else cr_1672_1673 k (by omega) h2
theorem cr_1673_1674 (k : ℕ) (h1 : 1673 ≤ k) (h2 : k < 1674) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1673 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1673_ok
theorem cr_1674_1675 (k : ℕ) (h1 : 1674 ≤ k) (h2 : k < 1675) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1674 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1674_ok
theorem cr_1675_1676 (k : ℕ) (h1 : 1675 ≤ k) (h2 : k < 1676) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1675 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1675_ok
theorem cr_1674_1676 (k : ℕ) (h1 : 1674 ≤ k) (h2 : k < 1676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1675 then cr_1674_1675 k h1 h else cr_1675_1676 k (by omega) h2
theorem cr_1673_1676 (k : ℕ) (h1 : 1673 ≤ k) (h2 : k < 1676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1674 then cr_1673_1674 k h1 h else cr_1674_1676 k (by omega) h2
theorem cr_1671_1676 (k : ℕ) (h1 : 1671 ≤ k) (h2 : k < 1676) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1673 then cr_1671_1673 k h1 h else cr_1673_1676 k (by omega) h2
theorem cr_1676_1677 (k : ℕ) (h1 : 1676 ≤ k) (h2 : k < 1677) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1676 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1676_ok
theorem cr_1677_1678 (k : ℕ) (h1 : 1677 ≤ k) (h2 : k < 1678) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1677 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1677_ok
theorem cr_1678_1679 (k : ℕ) (h1 : 1678 ≤ k) (h2 : k < 1679) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1678 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1678_ok
theorem cr_1677_1679 (k : ℕ) (h1 : 1677 ≤ k) (h2 : k < 1679) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1678 then cr_1677_1678 k h1 h else cr_1678_1679 k (by omega) h2
theorem cr_1676_1679 (k : ℕ) (h1 : 1676 ≤ k) (h2 : k < 1679) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1677 then cr_1676_1677 k h1 h else cr_1677_1679 k (by omega) h2
theorem cr_1679_1680 (k : ℕ) (h1 : 1679 ≤ k) (h2 : k < 1680) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1679 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1679_ok
theorem cr_1680_1681 (k : ℕ) (h1 : 1680 ≤ k) (h2 : k < 1681) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1680 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1680_ok
theorem cr_1681_1682 (k : ℕ) (h1 : 1681 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1681 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1681_ok
theorem cr_1680_1682 (k : ℕ) (h1 : 1680 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1681 then cr_1680_1681 k h1 h else cr_1681_1682 k (by omega) h2
theorem cr_1679_1682 (k : ℕ) (h1 : 1679 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1680 then cr_1679_1680 k h1 h else cr_1680_1682 k (by omega) h2
theorem cr_1676_1682 (k : ℕ) (h1 : 1676 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1679 then cr_1676_1679 k h1 h else cr_1679_1682 k (by omega) h2
theorem cr_1671_1682 (k : ℕ) (h1 : 1671 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1676 then cr_1671_1676 k h1 h else cr_1676_1682 k (by omega) h2
theorem cr_1661_1682 (k : ℕ) (h1 : 1661 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1671 then cr_1661_1671 k h1 h else cr_1671_1682 k (by omega) h2
theorem cr_1641_1682 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1682) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1661 then cr_1641_1661 k h1 h else cr_1661_1682 k (by omega) h2
theorem cr_1682_1683 (k : ℕ) (h1 : 1682 ≤ k) (h2 : k < 1683) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1682 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1682_ok
theorem cr_1683_1684 (k : ℕ) (h1 : 1683 ≤ k) (h2 : k < 1684) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1683 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1683_ok
theorem cr_1682_1684 (k : ℕ) (h1 : 1682 ≤ k) (h2 : k < 1684) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1683 then cr_1682_1683 k h1 h else cr_1683_1684 k (by omega) h2
theorem cr_1684_1685 (k : ℕ) (h1 : 1684 ≤ k) (h2 : k < 1685) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1684 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1684_ok
theorem cr_1685_1686 (k : ℕ) (h1 : 1685 ≤ k) (h2 : k < 1686) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1685 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1685_ok
theorem cr_1686_1687 (k : ℕ) (h1 : 1686 ≤ k) (h2 : k < 1687) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1686 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1686_ok
theorem cr_1685_1687 (k : ℕ) (h1 : 1685 ≤ k) (h2 : k < 1687) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1686 then cr_1685_1686 k h1 h else cr_1686_1687 k (by omega) h2
theorem cr_1684_1687 (k : ℕ) (h1 : 1684 ≤ k) (h2 : k < 1687) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1685 then cr_1684_1685 k h1 h else cr_1685_1687 k (by omega) h2
theorem cr_1682_1687 (k : ℕ) (h1 : 1682 ≤ k) (h2 : k < 1687) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1684 then cr_1682_1684 k h1 h else cr_1684_1687 k (by omega) h2
theorem cr_1687_1688 (k : ℕ) (h1 : 1687 ≤ k) (h2 : k < 1688) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1687 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1687_ok
theorem cr_1688_1689 (k : ℕ) (h1 : 1688 ≤ k) (h2 : k < 1689) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1688 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1688_ok
theorem cr_1687_1689 (k : ℕ) (h1 : 1687 ≤ k) (h2 : k < 1689) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1688 then cr_1687_1688 k h1 h else cr_1688_1689 k (by omega) h2
theorem cr_1689_1690 (k : ℕ) (h1 : 1689 ≤ k) (h2 : k < 1690) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1689 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1689_ok
theorem cr_1690_1691 (k : ℕ) (h1 : 1690 ≤ k) (h2 : k < 1691) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1690 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1690_ok
theorem cr_1691_1692 (k : ℕ) (h1 : 1691 ≤ k) (h2 : k < 1692) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1691 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1691_ok
theorem cr_1690_1692 (k : ℕ) (h1 : 1690 ≤ k) (h2 : k < 1692) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1691 then cr_1690_1691 k h1 h else cr_1691_1692 k (by omega) h2
theorem cr_1689_1692 (k : ℕ) (h1 : 1689 ≤ k) (h2 : k < 1692) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1690 then cr_1689_1690 k h1 h else cr_1690_1692 k (by omega) h2
theorem cr_1687_1692 (k : ℕ) (h1 : 1687 ≤ k) (h2 : k < 1692) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1689 then cr_1687_1689 k h1 h else cr_1689_1692 k (by omega) h2
theorem cr_1682_1692 (k : ℕ) (h1 : 1682 ≤ k) (h2 : k < 1692) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1687 then cr_1682_1687 k h1 h else cr_1687_1692 k (by omega) h2
theorem cr_1692_1693 (k : ℕ) (h1 : 1692 ≤ k) (h2 : k < 1693) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1692 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1692_ok
theorem cr_1693_1694 (k : ℕ) (h1 : 1693 ≤ k) (h2 : k < 1694) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1693 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1693_ok
theorem cr_1692_1694 (k : ℕ) (h1 : 1692 ≤ k) (h2 : k < 1694) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1693 then cr_1692_1693 k h1 h else cr_1693_1694 k (by omega) h2
theorem cr_1694_1695 (k : ℕ) (h1 : 1694 ≤ k) (h2 : k < 1695) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1694 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1694_ok
theorem cr_1695_1696 (k : ℕ) (h1 : 1695 ≤ k) (h2 : k < 1696) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1695 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1695_ok
theorem cr_1696_1697 (k : ℕ) (h1 : 1696 ≤ k) (h2 : k < 1697) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1696 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1696_ok
theorem cr_1695_1697 (k : ℕ) (h1 : 1695 ≤ k) (h2 : k < 1697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1696 then cr_1695_1696 k h1 h else cr_1696_1697 k (by omega) h2
theorem cr_1694_1697 (k : ℕ) (h1 : 1694 ≤ k) (h2 : k < 1697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1695 then cr_1694_1695 k h1 h else cr_1695_1697 k (by omega) h2
theorem cr_1692_1697 (k : ℕ) (h1 : 1692 ≤ k) (h2 : k < 1697) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1694 then cr_1692_1694 k h1 h else cr_1694_1697 k (by omega) h2
theorem cr_1697_1698 (k : ℕ) (h1 : 1697 ≤ k) (h2 : k < 1698) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1697 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1697_ok
theorem cr_1698_1699 (k : ℕ) (h1 : 1698 ≤ k) (h2 : k < 1699) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1698 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1698_ok
theorem cr_1697_1699 (k : ℕ) (h1 : 1697 ≤ k) (h2 : k < 1699) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1698 then cr_1697_1698 k h1 h else cr_1698_1699 k (by omega) h2
theorem cr_1699_1700 (k : ℕ) (h1 : 1699 ≤ k) (h2 : k < 1700) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1699 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1699_ok
theorem cr_1700_1701 (k : ℕ) (h1 : 1700 ≤ k) (h2 : k < 1701) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1700 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1700_ok
theorem cr_1701_1702 (k : ℕ) (h1 : 1701 ≤ k) (h2 : k < 1702) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1701 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1701_ok
theorem cr_1700_1702 (k : ℕ) (h1 : 1700 ≤ k) (h2 : k < 1702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1701 then cr_1700_1701 k h1 h else cr_1701_1702 k (by omega) h2
theorem cr_1699_1702 (k : ℕ) (h1 : 1699 ≤ k) (h2 : k < 1702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1700 then cr_1699_1700 k h1 h else cr_1700_1702 k (by omega) h2
theorem cr_1697_1702 (k : ℕ) (h1 : 1697 ≤ k) (h2 : k < 1702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1699 then cr_1697_1699 k h1 h else cr_1699_1702 k (by omega) h2
theorem cr_1692_1702 (k : ℕ) (h1 : 1692 ≤ k) (h2 : k < 1702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1697 then cr_1692_1697 k h1 h else cr_1697_1702 k (by omega) h2
theorem cr_1682_1702 (k : ℕ) (h1 : 1682 ≤ k) (h2 : k < 1702) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1692 then cr_1682_1692 k h1 h else cr_1692_1702 k (by omega) h2
theorem cr_1702_1703 (k : ℕ) (h1 : 1702 ≤ k) (h2 : k < 1703) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1702 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1702_ok
theorem cr_1703_1704 (k : ℕ) (h1 : 1703 ≤ k) (h2 : k < 1704) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1703 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1703_ok
theorem cr_1702_1704 (k : ℕ) (h1 : 1702 ≤ k) (h2 : k < 1704) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1703 then cr_1702_1703 k h1 h else cr_1703_1704 k (by omega) h2
theorem cr_1704_1705 (k : ℕ) (h1 : 1704 ≤ k) (h2 : k < 1705) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1704 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1704_ok
theorem cr_1705_1706 (k : ℕ) (h1 : 1705 ≤ k) (h2 : k < 1706) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1705 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1705_ok
theorem cr_1706_1707 (k : ℕ) (h1 : 1706 ≤ k) (h2 : k < 1707) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1706 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1706_ok
theorem cr_1705_1707 (k : ℕ) (h1 : 1705 ≤ k) (h2 : k < 1707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1706 then cr_1705_1706 k h1 h else cr_1706_1707 k (by omega) h2
theorem cr_1704_1707 (k : ℕ) (h1 : 1704 ≤ k) (h2 : k < 1707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1705 then cr_1704_1705 k h1 h else cr_1705_1707 k (by omega) h2
theorem cr_1702_1707 (k : ℕ) (h1 : 1702 ≤ k) (h2 : k < 1707) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1704 then cr_1702_1704 k h1 h else cr_1704_1707 k (by omega) h2
theorem cr_1707_1708 (k : ℕ) (h1 : 1707 ≤ k) (h2 : k < 1708) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1707 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1707_ok
theorem cr_1708_1709 (k : ℕ) (h1 : 1708 ≤ k) (h2 : k < 1709) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1708 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1708_ok
theorem cr_1707_1709 (k : ℕ) (h1 : 1707 ≤ k) (h2 : k < 1709) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1708 then cr_1707_1708 k h1 h else cr_1708_1709 k (by omega) h2
theorem cr_1709_1710 (k : ℕ) (h1 : 1709 ≤ k) (h2 : k < 1710) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1709 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1709_ok
theorem cr_1710_1711 (k : ℕ) (h1 : 1710 ≤ k) (h2 : k < 1711) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1710 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1710_ok
theorem cr_1711_1712 (k : ℕ) (h1 : 1711 ≤ k) (h2 : k < 1712) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1711 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1711_ok
theorem cr_1710_1712 (k : ℕ) (h1 : 1710 ≤ k) (h2 : k < 1712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1711 then cr_1710_1711 k h1 h else cr_1711_1712 k (by omega) h2
theorem cr_1709_1712 (k : ℕ) (h1 : 1709 ≤ k) (h2 : k < 1712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1710 then cr_1709_1710 k h1 h else cr_1710_1712 k (by omega) h2
theorem cr_1707_1712 (k : ℕ) (h1 : 1707 ≤ k) (h2 : k < 1712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1709 then cr_1707_1709 k h1 h else cr_1709_1712 k (by omega) h2
theorem cr_1702_1712 (k : ℕ) (h1 : 1702 ≤ k) (h2 : k < 1712) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1707 then cr_1702_1707 k h1 h else cr_1707_1712 k (by omega) h2
theorem cr_1712_1713 (k : ℕ) (h1 : 1712 ≤ k) (h2 : k < 1713) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1712 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1712_ok
theorem cr_1713_1714 (k : ℕ) (h1 : 1713 ≤ k) (h2 : k < 1714) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1713 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1713_ok
theorem cr_1712_1714 (k : ℕ) (h1 : 1712 ≤ k) (h2 : k < 1714) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1713 then cr_1712_1713 k h1 h else cr_1713_1714 k (by omega) h2
theorem cr_1714_1715 (k : ℕ) (h1 : 1714 ≤ k) (h2 : k < 1715) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1714 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1714_ok
theorem cr_1715_1716 (k : ℕ) (h1 : 1715 ≤ k) (h2 : k < 1716) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1715 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1715_ok
theorem cr_1716_1717 (k : ℕ) (h1 : 1716 ≤ k) (h2 : k < 1717) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1716 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1716_ok
theorem cr_1715_1717 (k : ℕ) (h1 : 1715 ≤ k) (h2 : k < 1717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1716 then cr_1715_1716 k h1 h else cr_1716_1717 k (by omega) h2
theorem cr_1714_1717 (k : ℕ) (h1 : 1714 ≤ k) (h2 : k < 1717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1715 then cr_1714_1715 k h1 h else cr_1715_1717 k (by omega) h2
theorem cr_1712_1717 (k : ℕ) (h1 : 1712 ≤ k) (h2 : k < 1717) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1714 then cr_1712_1714 k h1 h else cr_1714_1717 k (by omega) h2
theorem cr_1717_1718 (k : ℕ) (h1 : 1717 ≤ k) (h2 : k < 1718) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1717 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1717_ok
theorem cr_1718_1719 (k : ℕ) (h1 : 1718 ≤ k) (h2 : k < 1719) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1718 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1718_ok
theorem cr_1719_1720 (k : ℕ) (h1 : 1719 ≤ k) (h2 : k < 1720) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1719 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1719_ok
theorem cr_1718_1720 (k : ℕ) (h1 : 1718 ≤ k) (h2 : k < 1720) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1719 then cr_1718_1719 k h1 h else cr_1719_1720 k (by omega) h2
theorem cr_1717_1720 (k : ℕ) (h1 : 1717 ≤ k) (h2 : k < 1720) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1718 then cr_1717_1718 k h1 h else cr_1718_1720 k (by omega) h2
theorem cr_1720_1721 (k : ℕ) (h1 : 1720 ≤ k) (h2 : k < 1721) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1720 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1720_ok
theorem cr_1721_1722 (k : ℕ) (h1 : 1721 ≤ k) (h2 : k < 1722) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1721 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1721_ok
theorem cr_1722_1723 (k : ℕ) (h1 : 1722 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1722 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1722_ok
theorem cr_1721_1723 (k : ℕ) (h1 : 1721 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1722 then cr_1721_1722 k h1 h else cr_1722_1723 k (by omega) h2
theorem cr_1720_1723 (k : ℕ) (h1 : 1720 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1721 then cr_1720_1721 k h1 h else cr_1721_1723 k (by omega) h2
theorem cr_1717_1723 (k : ℕ) (h1 : 1717 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1720 then cr_1717_1720 k h1 h else cr_1720_1723 k (by omega) h2
theorem cr_1712_1723 (k : ℕ) (h1 : 1712 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1717 then cr_1712_1717 k h1 h else cr_1717_1723 k (by omega) h2
theorem cr_1702_1723 (k : ℕ) (h1 : 1702 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1712 then cr_1702_1712 k h1 h else cr_1712_1723 k (by omega) h2
theorem cr_1682_1723 (k : ℕ) (h1 : 1682 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1702 then cr_1682_1702 k h1 h else cr_1702_1723 k (by omega) h2
theorem cr_1641_1723 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1723) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1682 then cr_1641_1682 k h1 h else cr_1682_1723 k (by omega) h2
theorem cr_1723_1724 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1724) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1723 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1723_ok
theorem cr_1724_1725 (k : ℕ) (h1 : 1724 ≤ k) (h2 : k < 1725) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1724 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1724_ok
theorem cr_1723_1725 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1725) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1724 then cr_1723_1724 k h1 h else cr_1724_1725 k (by omega) h2
theorem cr_1725_1726 (k : ℕ) (h1 : 1725 ≤ k) (h2 : k < 1726) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1725 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1725_ok
theorem cr_1726_1727 (k : ℕ) (h1 : 1726 ≤ k) (h2 : k < 1727) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1726 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1726_ok
theorem cr_1727_1728 (k : ℕ) (h1 : 1727 ≤ k) (h2 : k < 1728) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1727 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1727_ok
theorem cr_1726_1728 (k : ℕ) (h1 : 1726 ≤ k) (h2 : k < 1728) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1727 then cr_1726_1727 k h1 h else cr_1727_1728 k (by omega) h2
theorem cr_1725_1728 (k : ℕ) (h1 : 1725 ≤ k) (h2 : k < 1728) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1726 then cr_1725_1726 k h1 h else cr_1726_1728 k (by omega) h2
theorem cr_1723_1728 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1728) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1725 then cr_1723_1725 k h1 h else cr_1725_1728 k (by omega) h2
theorem cr_1728_1729 (k : ℕ) (h1 : 1728 ≤ k) (h2 : k < 1729) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1728 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1728_ok
theorem cr_1729_1730 (k : ℕ) (h1 : 1729 ≤ k) (h2 : k < 1730) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1729 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1729_ok
theorem cr_1728_1730 (k : ℕ) (h1 : 1728 ≤ k) (h2 : k < 1730) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1729 then cr_1728_1729 k h1 h else cr_1729_1730 k (by omega) h2
theorem cr_1730_1731 (k : ℕ) (h1 : 1730 ≤ k) (h2 : k < 1731) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1730 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1730_ok
theorem cr_1731_1732 (k : ℕ) (h1 : 1731 ≤ k) (h2 : k < 1732) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1731 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1731_ok
theorem cr_1732_1733 (k : ℕ) (h1 : 1732 ≤ k) (h2 : k < 1733) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1732 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1732_ok
theorem cr_1731_1733 (k : ℕ) (h1 : 1731 ≤ k) (h2 : k < 1733) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1732 then cr_1731_1732 k h1 h else cr_1732_1733 k (by omega) h2
theorem cr_1730_1733 (k : ℕ) (h1 : 1730 ≤ k) (h2 : k < 1733) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1731 then cr_1730_1731 k h1 h else cr_1731_1733 k (by omega) h2
theorem cr_1728_1733 (k : ℕ) (h1 : 1728 ≤ k) (h2 : k < 1733) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1730 then cr_1728_1730 k h1 h else cr_1730_1733 k (by omega) h2
theorem cr_1723_1733 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1733) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1728 then cr_1723_1728 k h1 h else cr_1728_1733 k (by omega) h2
theorem cr_1733_1734 (k : ℕ) (h1 : 1733 ≤ k) (h2 : k < 1734) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1733 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1733_ok
theorem cr_1734_1735 (k : ℕ) (h1 : 1734 ≤ k) (h2 : k < 1735) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1734 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1734_ok
theorem cr_1733_1735 (k : ℕ) (h1 : 1733 ≤ k) (h2 : k < 1735) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1734 then cr_1733_1734 k h1 h else cr_1734_1735 k (by omega) h2
theorem cr_1735_1736 (k : ℕ) (h1 : 1735 ≤ k) (h2 : k < 1736) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1735 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1735_ok
theorem cr_1736_1737 (k : ℕ) (h1 : 1736 ≤ k) (h2 : k < 1737) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1736 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1736_ok
theorem cr_1737_1738 (k : ℕ) (h1 : 1737 ≤ k) (h2 : k < 1738) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1737 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1737_ok
theorem cr_1736_1738 (k : ℕ) (h1 : 1736 ≤ k) (h2 : k < 1738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1737 then cr_1736_1737 k h1 h else cr_1737_1738 k (by omega) h2
theorem cr_1735_1738 (k : ℕ) (h1 : 1735 ≤ k) (h2 : k < 1738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1736 then cr_1735_1736 k h1 h else cr_1736_1738 k (by omega) h2
theorem cr_1733_1738 (k : ℕ) (h1 : 1733 ≤ k) (h2 : k < 1738) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1735 then cr_1733_1735 k h1 h else cr_1735_1738 k (by omega) h2
theorem cr_1738_1739 (k : ℕ) (h1 : 1738 ≤ k) (h2 : k < 1739) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1738 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1738_ok
theorem cr_1739_1740 (k : ℕ) (h1 : 1739 ≤ k) (h2 : k < 1740) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1739 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1739_ok
theorem cr_1738_1740 (k : ℕ) (h1 : 1738 ≤ k) (h2 : k < 1740) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1739 then cr_1738_1739 k h1 h else cr_1739_1740 k (by omega) h2
theorem cr_1740_1741 (k : ℕ) (h1 : 1740 ≤ k) (h2 : k < 1741) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1740 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1740_ok
theorem cr_1741_1742 (k : ℕ) (h1 : 1741 ≤ k) (h2 : k < 1742) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1741 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1741_ok
theorem cr_1742_1743 (k : ℕ) (h1 : 1742 ≤ k) (h2 : k < 1743) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1742 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1742_ok
theorem cr_1741_1743 (k : ℕ) (h1 : 1741 ≤ k) (h2 : k < 1743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1742 then cr_1741_1742 k h1 h else cr_1742_1743 k (by omega) h2
theorem cr_1740_1743 (k : ℕ) (h1 : 1740 ≤ k) (h2 : k < 1743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1741 then cr_1740_1741 k h1 h else cr_1741_1743 k (by omega) h2
theorem cr_1738_1743 (k : ℕ) (h1 : 1738 ≤ k) (h2 : k < 1743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1740 then cr_1738_1740 k h1 h else cr_1740_1743 k (by omega) h2
theorem cr_1733_1743 (k : ℕ) (h1 : 1733 ≤ k) (h2 : k < 1743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1738 then cr_1733_1738 k h1 h else cr_1738_1743 k (by omega) h2
theorem cr_1723_1743 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1743) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1733 then cr_1723_1733 k h1 h else cr_1733_1743 k (by omega) h2
theorem cr_1743_1744 (k : ℕ) (h1 : 1743 ≤ k) (h2 : k < 1744) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1743 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1743_ok
theorem cr_1744_1745 (k : ℕ) (h1 : 1744 ≤ k) (h2 : k < 1745) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1744 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1744_ok
theorem cr_1743_1745 (k : ℕ) (h1 : 1743 ≤ k) (h2 : k < 1745) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1744 then cr_1743_1744 k h1 h else cr_1744_1745 k (by omega) h2
theorem cr_1745_1746 (k : ℕ) (h1 : 1745 ≤ k) (h2 : k < 1746) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1745 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1745_ok
theorem cr_1746_1747 (k : ℕ) (h1 : 1746 ≤ k) (h2 : k < 1747) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1746 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1746_ok
theorem cr_1747_1748 (k : ℕ) (h1 : 1747 ≤ k) (h2 : k < 1748) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1747 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1747_ok
theorem cr_1746_1748 (k : ℕ) (h1 : 1746 ≤ k) (h2 : k < 1748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1747 then cr_1746_1747 k h1 h else cr_1747_1748 k (by omega) h2
theorem cr_1745_1748 (k : ℕ) (h1 : 1745 ≤ k) (h2 : k < 1748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1746 then cr_1745_1746 k h1 h else cr_1746_1748 k (by omega) h2
theorem cr_1743_1748 (k : ℕ) (h1 : 1743 ≤ k) (h2 : k < 1748) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1745 then cr_1743_1745 k h1 h else cr_1745_1748 k (by omega) h2
theorem cr_1748_1749 (k : ℕ) (h1 : 1748 ≤ k) (h2 : k < 1749) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1748 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1748_ok
theorem cr_1749_1750 (k : ℕ) (h1 : 1749 ≤ k) (h2 : k < 1750) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1749 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1749_ok
theorem cr_1748_1750 (k : ℕ) (h1 : 1748 ≤ k) (h2 : k < 1750) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1749 then cr_1748_1749 k h1 h else cr_1749_1750 k (by omega) h2
theorem cr_1750_1751 (k : ℕ) (h1 : 1750 ≤ k) (h2 : k < 1751) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1750 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1750_ok
theorem cr_1751_1752 (k : ℕ) (h1 : 1751 ≤ k) (h2 : k < 1752) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1751 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1751_ok
theorem cr_1752_1753 (k : ℕ) (h1 : 1752 ≤ k) (h2 : k < 1753) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1752 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1752_ok
theorem cr_1751_1753 (k : ℕ) (h1 : 1751 ≤ k) (h2 : k < 1753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1752 then cr_1751_1752 k h1 h else cr_1752_1753 k (by omega) h2
theorem cr_1750_1753 (k : ℕ) (h1 : 1750 ≤ k) (h2 : k < 1753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1751 then cr_1750_1751 k h1 h else cr_1751_1753 k (by omega) h2
theorem cr_1748_1753 (k : ℕ) (h1 : 1748 ≤ k) (h2 : k < 1753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1750 then cr_1748_1750 k h1 h else cr_1750_1753 k (by omega) h2
theorem cr_1743_1753 (k : ℕ) (h1 : 1743 ≤ k) (h2 : k < 1753) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1748 then cr_1743_1748 k h1 h else cr_1748_1753 k (by omega) h2
theorem cr_1753_1754 (k : ℕ) (h1 : 1753 ≤ k) (h2 : k < 1754) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1753 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1753_ok
theorem cr_1754_1755 (k : ℕ) (h1 : 1754 ≤ k) (h2 : k < 1755) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1754 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1754_ok
theorem cr_1753_1755 (k : ℕ) (h1 : 1753 ≤ k) (h2 : k < 1755) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1754 then cr_1753_1754 k h1 h else cr_1754_1755 k (by omega) h2
theorem cr_1755_1756 (k : ℕ) (h1 : 1755 ≤ k) (h2 : k < 1756) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1755 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1755_ok
theorem cr_1756_1757 (k : ℕ) (h1 : 1756 ≤ k) (h2 : k < 1757) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1756 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1756_ok
theorem cr_1757_1758 (k : ℕ) (h1 : 1757 ≤ k) (h2 : k < 1758) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1757 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1757_ok
theorem cr_1756_1758 (k : ℕ) (h1 : 1756 ≤ k) (h2 : k < 1758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1757 then cr_1756_1757 k h1 h else cr_1757_1758 k (by omega) h2
theorem cr_1755_1758 (k : ℕ) (h1 : 1755 ≤ k) (h2 : k < 1758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1756 then cr_1755_1756 k h1 h else cr_1756_1758 k (by omega) h2
theorem cr_1753_1758 (k : ℕ) (h1 : 1753 ≤ k) (h2 : k < 1758) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1755 then cr_1753_1755 k h1 h else cr_1755_1758 k (by omega) h2
theorem cr_1758_1759 (k : ℕ) (h1 : 1758 ≤ k) (h2 : k < 1759) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1758 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1758_ok
theorem cr_1759_1760 (k : ℕ) (h1 : 1759 ≤ k) (h2 : k < 1760) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1759 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1759_ok
theorem cr_1760_1761 (k : ℕ) (h1 : 1760 ≤ k) (h2 : k < 1761) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1760 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1760_ok
theorem cr_1759_1761 (k : ℕ) (h1 : 1759 ≤ k) (h2 : k < 1761) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1760 then cr_1759_1760 k h1 h else cr_1760_1761 k (by omega) h2
theorem cr_1758_1761 (k : ℕ) (h1 : 1758 ≤ k) (h2 : k < 1761) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1759 then cr_1758_1759 k h1 h else cr_1759_1761 k (by omega) h2
theorem cr_1761_1762 (k : ℕ) (h1 : 1761 ≤ k) (h2 : k < 1762) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1761 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1761_ok
theorem cr_1762_1763 (k : ℕ) (h1 : 1762 ≤ k) (h2 : k < 1763) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1762 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1762_ok
theorem cr_1763_1764 (k : ℕ) (h1 : 1763 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1763 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1763_ok
theorem cr_1762_1764 (k : ℕ) (h1 : 1762 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1763 then cr_1762_1763 k h1 h else cr_1763_1764 k (by omega) h2
theorem cr_1761_1764 (k : ℕ) (h1 : 1761 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1762 then cr_1761_1762 k h1 h else cr_1762_1764 k (by omega) h2
theorem cr_1758_1764 (k : ℕ) (h1 : 1758 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1761 then cr_1758_1761 k h1 h else cr_1761_1764 k (by omega) h2
theorem cr_1753_1764 (k : ℕ) (h1 : 1753 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1758 then cr_1753_1758 k h1 h else cr_1758_1764 k (by omega) h2
theorem cr_1743_1764 (k : ℕ) (h1 : 1743 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1753 then cr_1743_1753 k h1 h else cr_1753_1764 k (by omega) h2
theorem cr_1723_1764 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1764) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1743 then cr_1723_1743 k h1 h else cr_1743_1764 k (by omega) h2
theorem cr_1764_1765 (k : ℕ) (h1 : 1764 ≤ k) (h2 : k < 1765) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1764 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1764_ok
theorem cr_1765_1766 (k : ℕ) (h1 : 1765 ≤ k) (h2 : k < 1766) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1765 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1765_ok
theorem cr_1764_1766 (k : ℕ) (h1 : 1764 ≤ k) (h2 : k < 1766) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1765 then cr_1764_1765 k h1 h else cr_1765_1766 k (by omega) h2
theorem cr_1766_1767 (k : ℕ) (h1 : 1766 ≤ k) (h2 : k < 1767) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1766 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1766_ok
theorem cr_1767_1768 (k : ℕ) (h1 : 1767 ≤ k) (h2 : k < 1768) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1767 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1767_ok
theorem cr_1768_1769 (k : ℕ) (h1 : 1768 ≤ k) (h2 : k < 1769) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1768 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1768_ok
theorem cr_1767_1769 (k : ℕ) (h1 : 1767 ≤ k) (h2 : k < 1769) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1768 then cr_1767_1768 k h1 h else cr_1768_1769 k (by omega) h2
theorem cr_1766_1769 (k : ℕ) (h1 : 1766 ≤ k) (h2 : k < 1769) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1767 then cr_1766_1767 k h1 h else cr_1767_1769 k (by omega) h2
theorem cr_1764_1769 (k : ℕ) (h1 : 1764 ≤ k) (h2 : k < 1769) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1766 then cr_1764_1766 k h1 h else cr_1766_1769 k (by omega) h2
theorem cr_1769_1770 (k : ℕ) (h1 : 1769 ≤ k) (h2 : k < 1770) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1769 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1769_ok
theorem cr_1770_1771 (k : ℕ) (h1 : 1770 ≤ k) (h2 : k < 1771) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1770 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1770_ok
theorem cr_1769_1771 (k : ℕ) (h1 : 1769 ≤ k) (h2 : k < 1771) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1770 then cr_1769_1770 k h1 h else cr_1770_1771 k (by omega) h2
theorem cr_1771_1772 (k : ℕ) (h1 : 1771 ≤ k) (h2 : k < 1772) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1771 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1771_ok
theorem cr_1772_1773 (k : ℕ) (h1 : 1772 ≤ k) (h2 : k < 1773) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1772 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1772_ok
theorem cr_1773_1774 (k : ℕ) (h1 : 1773 ≤ k) (h2 : k < 1774) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1773 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1773_ok
theorem cr_1772_1774 (k : ℕ) (h1 : 1772 ≤ k) (h2 : k < 1774) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1773 then cr_1772_1773 k h1 h else cr_1773_1774 k (by omega) h2
theorem cr_1771_1774 (k : ℕ) (h1 : 1771 ≤ k) (h2 : k < 1774) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1772 then cr_1771_1772 k h1 h else cr_1772_1774 k (by omega) h2
theorem cr_1769_1774 (k : ℕ) (h1 : 1769 ≤ k) (h2 : k < 1774) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1771 then cr_1769_1771 k h1 h else cr_1771_1774 k (by omega) h2
theorem cr_1764_1774 (k : ℕ) (h1 : 1764 ≤ k) (h2 : k < 1774) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1769 then cr_1764_1769 k h1 h else cr_1769_1774 k (by omega) h2
theorem cr_1774_1775 (k : ℕ) (h1 : 1774 ≤ k) (h2 : k < 1775) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1774 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1774_ok
theorem cr_1775_1776 (k : ℕ) (h1 : 1775 ≤ k) (h2 : k < 1776) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1775 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1775_ok
theorem cr_1774_1776 (k : ℕ) (h1 : 1774 ≤ k) (h2 : k < 1776) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1775 then cr_1774_1775 k h1 h else cr_1775_1776 k (by omega) h2
theorem cr_1776_1777 (k : ℕ) (h1 : 1776 ≤ k) (h2 : k < 1777) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1776 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1776_ok
theorem cr_1777_1778 (k : ℕ) (h1 : 1777 ≤ k) (h2 : k < 1778) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1777 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1777_ok
theorem cr_1778_1779 (k : ℕ) (h1 : 1778 ≤ k) (h2 : k < 1779) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1778 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1778_ok
theorem cr_1777_1779 (k : ℕ) (h1 : 1777 ≤ k) (h2 : k < 1779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1778 then cr_1777_1778 k h1 h else cr_1778_1779 k (by omega) h2
theorem cr_1776_1779 (k : ℕ) (h1 : 1776 ≤ k) (h2 : k < 1779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1777 then cr_1776_1777 k h1 h else cr_1777_1779 k (by omega) h2
theorem cr_1774_1779 (k : ℕ) (h1 : 1774 ≤ k) (h2 : k < 1779) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1776 then cr_1774_1776 k h1 h else cr_1776_1779 k (by omega) h2
theorem cr_1779_1780 (k : ℕ) (h1 : 1779 ≤ k) (h2 : k < 1780) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1779 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1779_ok
theorem cr_1780_1781 (k : ℕ) (h1 : 1780 ≤ k) (h2 : k < 1781) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1780 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1780_ok
theorem cr_1779_1781 (k : ℕ) (h1 : 1779 ≤ k) (h2 : k < 1781) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1780 then cr_1779_1780 k h1 h else cr_1780_1781 k (by omega) h2
theorem cr_1781_1782 (k : ℕ) (h1 : 1781 ≤ k) (h2 : k < 1782) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1781 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1781_ok
theorem cr_1782_1783 (k : ℕ) (h1 : 1782 ≤ k) (h2 : k < 1783) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1782 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1782_ok
theorem cr_1783_1784 (k : ℕ) (h1 : 1783 ≤ k) (h2 : k < 1784) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1783 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1783_ok
theorem cr_1782_1784 (k : ℕ) (h1 : 1782 ≤ k) (h2 : k < 1784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1783 then cr_1782_1783 k h1 h else cr_1783_1784 k (by omega) h2
theorem cr_1781_1784 (k : ℕ) (h1 : 1781 ≤ k) (h2 : k < 1784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1782 then cr_1781_1782 k h1 h else cr_1782_1784 k (by omega) h2
theorem cr_1779_1784 (k : ℕ) (h1 : 1779 ≤ k) (h2 : k < 1784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1781 then cr_1779_1781 k h1 h else cr_1781_1784 k (by omega) h2
theorem cr_1774_1784 (k : ℕ) (h1 : 1774 ≤ k) (h2 : k < 1784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1779 then cr_1774_1779 k h1 h else cr_1779_1784 k (by omega) h2
theorem cr_1764_1784 (k : ℕ) (h1 : 1764 ≤ k) (h2 : k < 1784) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1774 then cr_1764_1774 k h1 h else cr_1774_1784 k (by omega) h2
theorem cr_1784_1785 (k : ℕ) (h1 : 1784 ≤ k) (h2 : k < 1785) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1784 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1784_ok
theorem cr_1785_1786 (k : ℕ) (h1 : 1785 ≤ k) (h2 : k < 1786) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1785 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1785_ok
theorem cr_1784_1786 (k : ℕ) (h1 : 1784 ≤ k) (h2 : k < 1786) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1785 then cr_1784_1785 k h1 h else cr_1785_1786 k (by omega) h2
theorem cr_1786_1787 (k : ℕ) (h1 : 1786 ≤ k) (h2 : k < 1787) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1786 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1786_ok
theorem cr_1787_1788 (k : ℕ) (h1 : 1787 ≤ k) (h2 : k < 1788) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1787 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1787_ok
theorem cr_1788_1789 (k : ℕ) (h1 : 1788 ≤ k) (h2 : k < 1789) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1788 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1788_ok
theorem cr_1787_1789 (k : ℕ) (h1 : 1787 ≤ k) (h2 : k < 1789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1788 then cr_1787_1788 k h1 h else cr_1788_1789 k (by omega) h2
theorem cr_1786_1789 (k : ℕ) (h1 : 1786 ≤ k) (h2 : k < 1789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1787 then cr_1786_1787 k h1 h else cr_1787_1789 k (by omega) h2
theorem cr_1784_1789 (k : ℕ) (h1 : 1784 ≤ k) (h2 : k < 1789) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1786 then cr_1784_1786 k h1 h else cr_1786_1789 k (by omega) h2
theorem cr_1789_1790 (k : ℕ) (h1 : 1789 ≤ k) (h2 : k < 1790) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1789 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1789_ok
theorem cr_1790_1791 (k : ℕ) (h1 : 1790 ≤ k) (h2 : k < 1791) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1790 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1790_ok
theorem cr_1789_1791 (k : ℕ) (h1 : 1789 ≤ k) (h2 : k < 1791) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1790 then cr_1789_1790 k h1 h else cr_1790_1791 k (by omega) h2
theorem cr_1791_1792 (k : ℕ) (h1 : 1791 ≤ k) (h2 : k < 1792) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1791 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1791_ok
theorem cr_1792_1793 (k : ℕ) (h1 : 1792 ≤ k) (h2 : k < 1793) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1792 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1792_ok
theorem cr_1793_1794 (k : ℕ) (h1 : 1793 ≤ k) (h2 : k < 1794) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1793 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1793_ok
theorem cr_1792_1794 (k : ℕ) (h1 : 1792 ≤ k) (h2 : k < 1794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1793 then cr_1792_1793 k h1 h else cr_1793_1794 k (by omega) h2
theorem cr_1791_1794 (k : ℕ) (h1 : 1791 ≤ k) (h2 : k < 1794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1792 then cr_1791_1792 k h1 h else cr_1792_1794 k (by omega) h2
theorem cr_1789_1794 (k : ℕ) (h1 : 1789 ≤ k) (h2 : k < 1794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1791 then cr_1789_1791 k h1 h else cr_1791_1794 k (by omega) h2
theorem cr_1784_1794 (k : ℕ) (h1 : 1784 ≤ k) (h2 : k < 1794) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1789 then cr_1784_1789 k h1 h else cr_1789_1794 k (by omega) h2
theorem cr_1794_1795 (k : ℕ) (h1 : 1794 ≤ k) (h2 : k < 1795) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1794 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1794_ok
theorem cr_1795_1796 (k : ℕ) (h1 : 1795 ≤ k) (h2 : k < 1796) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1795 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1795_ok
theorem cr_1794_1796 (k : ℕ) (h1 : 1794 ≤ k) (h2 : k < 1796) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1795 then cr_1794_1795 k h1 h else cr_1795_1796 k (by omega) h2
theorem cr_1796_1797 (k : ℕ) (h1 : 1796 ≤ k) (h2 : k < 1797) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1796 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1796_ok
theorem cr_1797_1798 (k : ℕ) (h1 : 1797 ≤ k) (h2 : k < 1798) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1797 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1797_ok
theorem cr_1798_1799 (k : ℕ) (h1 : 1798 ≤ k) (h2 : k < 1799) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1798 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1798_ok
theorem cr_1797_1799 (k : ℕ) (h1 : 1797 ≤ k) (h2 : k < 1799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1798 then cr_1797_1798 k h1 h else cr_1798_1799 k (by omega) h2
theorem cr_1796_1799 (k : ℕ) (h1 : 1796 ≤ k) (h2 : k < 1799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1797 then cr_1796_1797 k h1 h else cr_1797_1799 k (by omega) h2
theorem cr_1794_1799 (k : ℕ) (h1 : 1794 ≤ k) (h2 : k < 1799) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1796 then cr_1794_1796 k h1 h else cr_1796_1799 k (by omega) h2
theorem cr_1799_1800 (k : ℕ) (h1 : 1799 ≤ k) (h2 : k < 1800) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1799 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1799_ok
theorem cr_1800_1801 (k : ℕ) (h1 : 1800 ≤ k) (h2 : k < 1801) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1800 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1800_ok
theorem cr_1801_1802 (k : ℕ) (h1 : 1801 ≤ k) (h2 : k < 1802) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1801 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1801_ok
theorem cr_1800_1802 (k : ℕ) (h1 : 1800 ≤ k) (h2 : k < 1802) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1801 then cr_1800_1801 k h1 h else cr_1801_1802 k (by omega) h2
theorem cr_1799_1802 (k : ℕ) (h1 : 1799 ≤ k) (h2 : k < 1802) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1800 then cr_1799_1800 k h1 h else cr_1800_1802 k (by omega) h2
theorem cr_1802_1803 (k : ℕ) (h1 : 1802 ≤ k) (h2 : k < 1803) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1802 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1802_ok
theorem cr_1803_1804 (k : ℕ) (h1 : 1803 ≤ k) (h2 : k < 1804) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1803 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1803_ok
theorem cr_1804_1805 (k : ℕ) (h1 : 1804 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1804 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1804_ok
theorem cr_1803_1805 (k : ℕ) (h1 : 1803 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1804 then cr_1803_1804 k h1 h else cr_1804_1805 k (by omega) h2
theorem cr_1802_1805 (k : ℕ) (h1 : 1802 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1803 then cr_1802_1803 k h1 h else cr_1803_1805 k (by omega) h2
theorem cr_1799_1805 (k : ℕ) (h1 : 1799 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1802 then cr_1799_1802 k h1 h else cr_1802_1805 k (by omega) h2
theorem cr_1794_1805 (k : ℕ) (h1 : 1794 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1799 then cr_1794_1799 k h1 h else cr_1799_1805 k (by omega) h2
theorem cr_1784_1805 (k : ℕ) (h1 : 1784 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1794 then cr_1784_1794 k h1 h else cr_1794_1805 k (by omega) h2
theorem cr_1764_1805 (k : ℕ) (h1 : 1764 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1784 then cr_1764_1784 k h1 h else cr_1784_1805 k (by omega) h2
theorem cr_1723_1805 (k : ℕ) (h1 : 1723 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1764 then cr_1723_1764 k h1 h else cr_1764_1805 k (by omega) h2
theorem cr_1641_1805 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1805) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1723 then cr_1641_1723 k h1 h else cr_1723_1805 k (by omega) h2
theorem cr_1805_1806 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1806) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1805 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1805_ok
theorem cr_1806_1807 (k : ℕ) (h1 : 1806 ≤ k) (h2 : k < 1807) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1806 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1806_ok
theorem cr_1805_1807 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1807) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1806 then cr_1805_1806 k h1 h else cr_1806_1807 k (by omega) h2
theorem cr_1807_1808 (k : ℕ) (h1 : 1807 ≤ k) (h2 : k < 1808) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1807 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1807_ok
theorem cr_1808_1809 (k : ℕ) (h1 : 1808 ≤ k) (h2 : k < 1809) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1808 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1808_ok
theorem cr_1809_1810 (k : ℕ) (h1 : 1809 ≤ k) (h2 : k < 1810) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1809 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1809_ok
theorem cr_1808_1810 (k : ℕ) (h1 : 1808 ≤ k) (h2 : k < 1810) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1809 then cr_1808_1809 k h1 h else cr_1809_1810 k (by omega) h2
theorem cr_1807_1810 (k : ℕ) (h1 : 1807 ≤ k) (h2 : k < 1810) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1808 then cr_1807_1808 k h1 h else cr_1808_1810 k (by omega) h2
theorem cr_1805_1810 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1810) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1807 then cr_1805_1807 k h1 h else cr_1807_1810 k (by omega) h2
theorem cr_1810_1811 (k : ℕ) (h1 : 1810 ≤ k) (h2 : k < 1811) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1810 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1810_ok
theorem cr_1811_1812 (k : ℕ) (h1 : 1811 ≤ k) (h2 : k < 1812) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1811 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1811_ok
theorem cr_1810_1812 (k : ℕ) (h1 : 1810 ≤ k) (h2 : k < 1812) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1811 then cr_1810_1811 k h1 h else cr_1811_1812 k (by omega) h2
theorem cr_1812_1813 (k : ℕ) (h1 : 1812 ≤ k) (h2 : k < 1813) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1812 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1812_ok
theorem cr_1813_1814 (k : ℕ) (h1 : 1813 ≤ k) (h2 : k < 1814) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1813 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1813_ok
theorem cr_1814_1815 (k : ℕ) (h1 : 1814 ≤ k) (h2 : k < 1815) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1814 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1814_ok
theorem cr_1813_1815 (k : ℕ) (h1 : 1813 ≤ k) (h2 : k < 1815) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1814 then cr_1813_1814 k h1 h else cr_1814_1815 k (by omega) h2
theorem cr_1812_1815 (k : ℕ) (h1 : 1812 ≤ k) (h2 : k < 1815) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1813 then cr_1812_1813 k h1 h else cr_1813_1815 k (by omega) h2
theorem cr_1810_1815 (k : ℕ) (h1 : 1810 ≤ k) (h2 : k < 1815) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1812 then cr_1810_1812 k h1 h else cr_1812_1815 k (by omega) h2
theorem cr_1805_1815 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1815) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1810 then cr_1805_1810 k h1 h else cr_1810_1815 k (by omega) h2
theorem cr_1815_1816 (k : ℕ) (h1 : 1815 ≤ k) (h2 : k < 1816) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1815 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1815_ok
theorem cr_1816_1817 (k : ℕ) (h1 : 1816 ≤ k) (h2 : k < 1817) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1816 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1816_ok
theorem cr_1815_1817 (k : ℕ) (h1 : 1815 ≤ k) (h2 : k < 1817) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1816 then cr_1815_1816 k h1 h else cr_1816_1817 k (by omega) h2
theorem cr_1817_1818 (k : ℕ) (h1 : 1817 ≤ k) (h2 : k < 1818) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1817 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1817_ok
theorem cr_1818_1819 (k : ℕ) (h1 : 1818 ≤ k) (h2 : k < 1819) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1818 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1818_ok
theorem cr_1819_1820 (k : ℕ) (h1 : 1819 ≤ k) (h2 : k < 1820) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1819 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1819_ok
theorem cr_1818_1820 (k : ℕ) (h1 : 1818 ≤ k) (h2 : k < 1820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1819 then cr_1818_1819 k h1 h else cr_1819_1820 k (by omega) h2
theorem cr_1817_1820 (k : ℕ) (h1 : 1817 ≤ k) (h2 : k < 1820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1818 then cr_1817_1818 k h1 h else cr_1818_1820 k (by omega) h2
theorem cr_1815_1820 (k : ℕ) (h1 : 1815 ≤ k) (h2 : k < 1820) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1817 then cr_1815_1817 k h1 h else cr_1817_1820 k (by omega) h2
theorem cr_1820_1821 (k : ℕ) (h1 : 1820 ≤ k) (h2 : k < 1821) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1820 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1820_ok
theorem cr_1821_1822 (k : ℕ) (h1 : 1821 ≤ k) (h2 : k < 1822) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1821 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1821_ok
theorem cr_1820_1822 (k : ℕ) (h1 : 1820 ≤ k) (h2 : k < 1822) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1821 then cr_1820_1821 k h1 h else cr_1821_1822 k (by omega) h2
theorem cr_1822_1823 (k : ℕ) (h1 : 1822 ≤ k) (h2 : k < 1823) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1822 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1822_ok
theorem cr_1823_1824 (k : ℕ) (h1 : 1823 ≤ k) (h2 : k < 1824) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1823 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1823_ok
theorem cr_1824_1825 (k : ℕ) (h1 : 1824 ≤ k) (h2 : k < 1825) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1824 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1824_ok
theorem cr_1823_1825 (k : ℕ) (h1 : 1823 ≤ k) (h2 : k < 1825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1824 then cr_1823_1824 k h1 h else cr_1824_1825 k (by omega) h2
theorem cr_1822_1825 (k : ℕ) (h1 : 1822 ≤ k) (h2 : k < 1825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1823 then cr_1822_1823 k h1 h else cr_1823_1825 k (by omega) h2
theorem cr_1820_1825 (k : ℕ) (h1 : 1820 ≤ k) (h2 : k < 1825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1822 then cr_1820_1822 k h1 h else cr_1822_1825 k (by omega) h2
theorem cr_1815_1825 (k : ℕ) (h1 : 1815 ≤ k) (h2 : k < 1825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1820 then cr_1815_1820 k h1 h else cr_1820_1825 k (by omega) h2
theorem cr_1805_1825 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1825) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1815 then cr_1805_1815 k h1 h else cr_1815_1825 k (by omega) h2
theorem cr_1825_1826 (k : ℕ) (h1 : 1825 ≤ k) (h2 : k < 1826) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1825 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1825_ok
theorem cr_1826_1827 (k : ℕ) (h1 : 1826 ≤ k) (h2 : k < 1827) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1826 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1826_ok
theorem cr_1825_1827 (k : ℕ) (h1 : 1825 ≤ k) (h2 : k < 1827) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1826 then cr_1825_1826 k h1 h else cr_1826_1827 k (by omega) h2
theorem cr_1827_1828 (k : ℕ) (h1 : 1827 ≤ k) (h2 : k < 1828) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1827 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1827_ok
theorem cr_1828_1829 (k : ℕ) (h1 : 1828 ≤ k) (h2 : k < 1829) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1828 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1828_ok
theorem cr_1829_1830 (k : ℕ) (h1 : 1829 ≤ k) (h2 : k < 1830) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1829 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1829_ok
theorem cr_1828_1830 (k : ℕ) (h1 : 1828 ≤ k) (h2 : k < 1830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1829 then cr_1828_1829 k h1 h else cr_1829_1830 k (by omega) h2
theorem cr_1827_1830 (k : ℕ) (h1 : 1827 ≤ k) (h2 : k < 1830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1828 then cr_1827_1828 k h1 h else cr_1828_1830 k (by omega) h2
theorem cr_1825_1830 (k : ℕ) (h1 : 1825 ≤ k) (h2 : k < 1830) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1827 then cr_1825_1827 k h1 h else cr_1827_1830 k (by omega) h2
theorem cr_1830_1831 (k : ℕ) (h1 : 1830 ≤ k) (h2 : k < 1831) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1830 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1830_ok
theorem cr_1831_1832 (k : ℕ) (h1 : 1831 ≤ k) (h2 : k < 1832) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1831 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1831_ok
theorem cr_1830_1832 (k : ℕ) (h1 : 1830 ≤ k) (h2 : k < 1832) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1831 then cr_1830_1831 k h1 h else cr_1831_1832 k (by omega) h2
theorem cr_1832_1833 (k : ℕ) (h1 : 1832 ≤ k) (h2 : k < 1833) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1832 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1832_ok
theorem cr_1833_1834 (k : ℕ) (h1 : 1833 ≤ k) (h2 : k < 1834) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1833 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1833_ok
theorem cr_1834_1835 (k : ℕ) (h1 : 1834 ≤ k) (h2 : k < 1835) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1834 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1834_ok
theorem cr_1833_1835 (k : ℕ) (h1 : 1833 ≤ k) (h2 : k < 1835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1834 then cr_1833_1834 k h1 h else cr_1834_1835 k (by omega) h2
theorem cr_1832_1835 (k : ℕ) (h1 : 1832 ≤ k) (h2 : k < 1835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1833 then cr_1832_1833 k h1 h else cr_1833_1835 k (by omega) h2
theorem cr_1830_1835 (k : ℕ) (h1 : 1830 ≤ k) (h2 : k < 1835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1832 then cr_1830_1832 k h1 h else cr_1832_1835 k (by omega) h2
theorem cr_1825_1835 (k : ℕ) (h1 : 1825 ≤ k) (h2 : k < 1835) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1830 then cr_1825_1830 k h1 h else cr_1830_1835 k (by omega) h2
theorem cr_1835_1836 (k : ℕ) (h1 : 1835 ≤ k) (h2 : k < 1836) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1835 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1835_ok
theorem cr_1836_1837 (k : ℕ) (h1 : 1836 ≤ k) (h2 : k < 1837) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1836 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1836_ok
theorem cr_1835_1837 (k : ℕ) (h1 : 1835 ≤ k) (h2 : k < 1837) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1836 then cr_1835_1836 k h1 h else cr_1836_1837 k (by omega) h2
theorem cr_1837_1838 (k : ℕ) (h1 : 1837 ≤ k) (h2 : k < 1838) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1837 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1837_ok
theorem cr_1838_1839 (k : ℕ) (h1 : 1838 ≤ k) (h2 : k < 1839) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1838 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1838_ok
theorem cr_1839_1840 (k : ℕ) (h1 : 1839 ≤ k) (h2 : k < 1840) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1839 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1839_ok
theorem cr_1838_1840 (k : ℕ) (h1 : 1838 ≤ k) (h2 : k < 1840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1839 then cr_1838_1839 k h1 h else cr_1839_1840 k (by omega) h2
theorem cr_1837_1840 (k : ℕ) (h1 : 1837 ≤ k) (h2 : k < 1840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1838 then cr_1837_1838 k h1 h else cr_1838_1840 k (by omega) h2
theorem cr_1835_1840 (k : ℕ) (h1 : 1835 ≤ k) (h2 : k < 1840) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1837 then cr_1835_1837 k h1 h else cr_1837_1840 k (by omega) h2
theorem cr_1840_1841 (k : ℕ) (h1 : 1840 ≤ k) (h2 : k < 1841) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1840 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1840_ok
theorem cr_1841_1842 (k : ℕ) (h1 : 1841 ≤ k) (h2 : k < 1842) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1841 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1841_ok
theorem cr_1842_1843 (k : ℕ) (h1 : 1842 ≤ k) (h2 : k < 1843) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1842 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1842_ok
theorem cr_1841_1843 (k : ℕ) (h1 : 1841 ≤ k) (h2 : k < 1843) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1842 then cr_1841_1842 k h1 h else cr_1842_1843 k (by omega) h2
theorem cr_1840_1843 (k : ℕ) (h1 : 1840 ≤ k) (h2 : k < 1843) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1841 then cr_1840_1841 k h1 h else cr_1841_1843 k (by omega) h2
theorem cr_1843_1844 (k : ℕ) (h1 : 1843 ≤ k) (h2 : k < 1844) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1843 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1843_ok
theorem cr_1844_1845 (k : ℕ) (h1 : 1844 ≤ k) (h2 : k < 1845) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1844 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1844_ok
theorem cr_1845_1846 (k : ℕ) (h1 : 1845 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1845 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1845_ok
theorem cr_1844_1846 (k : ℕ) (h1 : 1844 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1845 then cr_1844_1845 k h1 h else cr_1845_1846 k (by omega) h2
theorem cr_1843_1846 (k : ℕ) (h1 : 1843 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1844 then cr_1843_1844 k h1 h else cr_1844_1846 k (by omega) h2
theorem cr_1840_1846 (k : ℕ) (h1 : 1840 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1843 then cr_1840_1843 k h1 h else cr_1843_1846 k (by omega) h2
theorem cr_1835_1846 (k : ℕ) (h1 : 1835 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1840 then cr_1835_1840 k h1 h else cr_1840_1846 k (by omega) h2
theorem cr_1825_1846 (k : ℕ) (h1 : 1825 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1835 then cr_1825_1835 k h1 h else cr_1835_1846 k (by omega) h2
theorem cr_1805_1846 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1846) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1825 then cr_1805_1825 k h1 h else cr_1825_1846 k (by omega) h2
theorem cr_1846_1847 (k : ℕ) (h1 : 1846 ≤ k) (h2 : k < 1847) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1846 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1846_ok
theorem cr_1847_1848 (k : ℕ) (h1 : 1847 ≤ k) (h2 : k < 1848) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1847 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1847_ok
theorem cr_1846_1848 (k : ℕ) (h1 : 1846 ≤ k) (h2 : k < 1848) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1847 then cr_1846_1847 k h1 h else cr_1847_1848 k (by omega) h2
theorem cr_1848_1849 (k : ℕ) (h1 : 1848 ≤ k) (h2 : k < 1849) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1848 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1848_ok
theorem cr_1849_1850 (k : ℕ) (h1 : 1849 ≤ k) (h2 : k < 1850) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1849 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1849_ok
theorem cr_1850_1851 (k : ℕ) (h1 : 1850 ≤ k) (h2 : k < 1851) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1850 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1850_ok
theorem cr_1849_1851 (k : ℕ) (h1 : 1849 ≤ k) (h2 : k < 1851) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1850 then cr_1849_1850 k h1 h else cr_1850_1851 k (by omega) h2
theorem cr_1848_1851 (k : ℕ) (h1 : 1848 ≤ k) (h2 : k < 1851) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1849 then cr_1848_1849 k h1 h else cr_1849_1851 k (by omega) h2
theorem cr_1846_1851 (k : ℕ) (h1 : 1846 ≤ k) (h2 : k < 1851) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1848 then cr_1846_1848 k h1 h else cr_1848_1851 k (by omega) h2
theorem cr_1851_1852 (k : ℕ) (h1 : 1851 ≤ k) (h2 : k < 1852) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1851 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1851_ok
theorem cr_1852_1853 (k : ℕ) (h1 : 1852 ≤ k) (h2 : k < 1853) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1852 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1852_ok
theorem cr_1851_1853 (k : ℕ) (h1 : 1851 ≤ k) (h2 : k < 1853) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1852 then cr_1851_1852 k h1 h else cr_1852_1853 k (by omega) h2
theorem cr_1853_1854 (k : ℕ) (h1 : 1853 ≤ k) (h2 : k < 1854) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1853 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1853_ok
theorem cr_1854_1855 (k : ℕ) (h1 : 1854 ≤ k) (h2 : k < 1855) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1854 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1854_ok
theorem cr_1855_1856 (k : ℕ) (h1 : 1855 ≤ k) (h2 : k < 1856) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1855 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1855_ok
theorem cr_1854_1856 (k : ℕ) (h1 : 1854 ≤ k) (h2 : k < 1856) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1855 then cr_1854_1855 k h1 h else cr_1855_1856 k (by omega) h2
theorem cr_1853_1856 (k : ℕ) (h1 : 1853 ≤ k) (h2 : k < 1856) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1854 then cr_1853_1854 k h1 h else cr_1854_1856 k (by omega) h2
theorem cr_1851_1856 (k : ℕ) (h1 : 1851 ≤ k) (h2 : k < 1856) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1853 then cr_1851_1853 k h1 h else cr_1853_1856 k (by omega) h2
theorem cr_1846_1856 (k : ℕ) (h1 : 1846 ≤ k) (h2 : k < 1856) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1851 then cr_1846_1851 k h1 h else cr_1851_1856 k (by omega) h2
theorem cr_1856_1857 (k : ℕ) (h1 : 1856 ≤ k) (h2 : k < 1857) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1856 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1856_ok
theorem cr_1857_1858 (k : ℕ) (h1 : 1857 ≤ k) (h2 : k < 1858) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1857 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1857_ok
theorem cr_1856_1858 (k : ℕ) (h1 : 1856 ≤ k) (h2 : k < 1858) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1857 then cr_1856_1857 k h1 h else cr_1857_1858 k (by omega) h2
theorem cr_1858_1859 (k : ℕ) (h1 : 1858 ≤ k) (h2 : k < 1859) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1858 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1858_ok
theorem cr_1859_1860 (k : ℕ) (h1 : 1859 ≤ k) (h2 : k < 1860) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1859 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1859_ok
theorem cr_1860_1861 (k : ℕ) (h1 : 1860 ≤ k) (h2 : k < 1861) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1860 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1860_ok
theorem cr_1859_1861 (k : ℕ) (h1 : 1859 ≤ k) (h2 : k < 1861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1860 then cr_1859_1860 k h1 h else cr_1860_1861 k (by omega) h2
theorem cr_1858_1861 (k : ℕ) (h1 : 1858 ≤ k) (h2 : k < 1861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1859 then cr_1858_1859 k h1 h else cr_1859_1861 k (by omega) h2
theorem cr_1856_1861 (k : ℕ) (h1 : 1856 ≤ k) (h2 : k < 1861) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1858 then cr_1856_1858 k h1 h else cr_1858_1861 k (by omega) h2
theorem cr_1861_1862 (k : ℕ) (h1 : 1861 ≤ k) (h2 : k < 1862) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1861 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1861_ok
theorem cr_1862_1863 (k : ℕ) (h1 : 1862 ≤ k) (h2 : k < 1863) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1862 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1862_ok
theorem cr_1861_1863 (k : ℕ) (h1 : 1861 ≤ k) (h2 : k < 1863) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1862 then cr_1861_1862 k h1 h else cr_1862_1863 k (by omega) h2
theorem cr_1863_1864 (k : ℕ) (h1 : 1863 ≤ k) (h2 : k < 1864) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1863 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1863_ok
theorem cr_1864_1865 (k : ℕ) (h1 : 1864 ≤ k) (h2 : k < 1865) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1864 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1864_ok
theorem cr_1865_1866 (k : ℕ) (h1 : 1865 ≤ k) (h2 : k < 1866) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1865 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1865_ok
theorem cr_1864_1866 (k : ℕ) (h1 : 1864 ≤ k) (h2 : k < 1866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1865 then cr_1864_1865 k h1 h else cr_1865_1866 k (by omega) h2
theorem cr_1863_1866 (k : ℕ) (h1 : 1863 ≤ k) (h2 : k < 1866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1864 then cr_1863_1864 k h1 h else cr_1864_1866 k (by omega) h2
theorem cr_1861_1866 (k : ℕ) (h1 : 1861 ≤ k) (h2 : k < 1866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1863 then cr_1861_1863 k h1 h else cr_1863_1866 k (by omega) h2
theorem cr_1856_1866 (k : ℕ) (h1 : 1856 ≤ k) (h2 : k < 1866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1861 then cr_1856_1861 k h1 h else cr_1861_1866 k (by omega) h2
theorem cr_1846_1866 (k : ℕ) (h1 : 1846 ≤ k) (h2 : k < 1866) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1856 then cr_1846_1856 k h1 h else cr_1856_1866 k (by omega) h2
theorem cr_1866_1867 (k : ℕ) (h1 : 1866 ≤ k) (h2 : k < 1867) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1866 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1866_ok
theorem cr_1867_1868 (k : ℕ) (h1 : 1867 ≤ k) (h2 : k < 1868) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1867 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1867_ok
theorem cr_1866_1868 (k : ℕ) (h1 : 1866 ≤ k) (h2 : k < 1868) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1867 then cr_1866_1867 k h1 h else cr_1867_1868 k (by omega) h2
theorem cr_1868_1869 (k : ℕ) (h1 : 1868 ≤ k) (h2 : k < 1869) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1868 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1868_ok
theorem cr_1869_1870 (k : ℕ) (h1 : 1869 ≤ k) (h2 : k < 1870) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1869 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1869_ok
theorem cr_1870_1871 (k : ℕ) (h1 : 1870 ≤ k) (h2 : k < 1871) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1870 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1870_ok
theorem cr_1869_1871 (k : ℕ) (h1 : 1869 ≤ k) (h2 : k < 1871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1870 then cr_1869_1870 k h1 h else cr_1870_1871 k (by omega) h2
theorem cr_1868_1871 (k : ℕ) (h1 : 1868 ≤ k) (h2 : k < 1871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1869 then cr_1868_1869 k h1 h else cr_1869_1871 k (by omega) h2
theorem cr_1866_1871 (k : ℕ) (h1 : 1866 ≤ k) (h2 : k < 1871) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1868 then cr_1866_1868 k h1 h else cr_1868_1871 k (by omega) h2
theorem cr_1871_1872 (k : ℕ) (h1 : 1871 ≤ k) (h2 : k < 1872) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1871 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1871_ok
theorem cr_1872_1873 (k : ℕ) (h1 : 1872 ≤ k) (h2 : k < 1873) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1872 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1872_ok
theorem cr_1871_1873 (k : ℕ) (h1 : 1871 ≤ k) (h2 : k < 1873) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1872 then cr_1871_1872 k h1 h else cr_1872_1873 k (by omega) h2
theorem cr_1873_1874 (k : ℕ) (h1 : 1873 ≤ k) (h2 : k < 1874) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1873 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1873_ok
theorem cr_1874_1875 (k : ℕ) (h1 : 1874 ≤ k) (h2 : k < 1875) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1874 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1874_ok
theorem cr_1875_1876 (k : ℕ) (h1 : 1875 ≤ k) (h2 : k < 1876) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1875 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1875_ok
theorem cr_1874_1876 (k : ℕ) (h1 : 1874 ≤ k) (h2 : k < 1876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1875 then cr_1874_1875 k h1 h else cr_1875_1876 k (by omega) h2
theorem cr_1873_1876 (k : ℕ) (h1 : 1873 ≤ k) (h2 : k < 1876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1874 then cr_1873_1874 k h1 h else cr_1874_1876 k (by omega) h2
theorem cr_1871_1876 (k : ℕ) (h1 : 1871 ≤ k) (h2 : k < 1876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1873 then cr_1871_1873 k h1 h else cr_1873_1876 k (by omega) h2
theorem cr_1866_1876 (k : ℕ) (h1 : 1866 ≤ k) (h2 : k < 1876) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1871 then cr_1866_1871 k h1 h else cr_1871_1876 k (by omega) h2
theorem cr_1876_1877 (k : ℕ) (h1 : 1876 ≤ k) (h2 : k < 1877) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1876 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1876_ok
theorem cr_1877_1878 (k : ℕ) (h1 : 1877 ≤ k) (h2 : k < 1878) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1877 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1877_ok
theorem cr_1876_1878 (k : ℕ) (h1 : 1876 ≤ k) (h2 : k < 1878) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1877 then cr_1876_1877 k h1 h else cr_1877_1878 k (by omega) h2
theorem cr_1878_1879 (k : ℕ) (h1 : 1878 ≤ k) (h2 : k < 1879) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1878 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1878_ok
theorem cr_1879_1880 (k : ℕ) (h1 : 1879 ≤ k) (h2 : k < 1880) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1879 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1879_ok
theorem cr_1880_1881 (k : ℕ) (h1 : 1880 ≤ k) (h2 : k < 1881) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1880 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1880_ok
theorem cr_1879_1881 (k : ℕ) (h1 : 1879 ≤ k) (h2 : k < 1881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1880 then cr_1879_1880 k h1 h else cr_1880_1881 k (by omega) h2
theorem cr_1878_1881 (k : ℕ) (h1 : 1878 ≤ k) (h2 : k < 1881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1879 then cr_1878_1879 k h1 h else cr_1879_1881 k (by omega) h2
theorem cr_1876_1881 (k : ℕ) (h1 : 1876 ≤ k) (h2 : k < 1881) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1878 then cr_1876_1878 k h1 h else cr_1878_1881 k (by omega) h2
theorem cr_1881_1882 (k : ℕ) (h1 : 1881 ≤ k) (h2 : k < 1882) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1881 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1881_ok
theorem cr_1882_1883 (k : ℕ) (h1 : 1882 ≤ k) (h2 : k < 1883) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1882 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1882_ok
theorem cr_1883_1884 (k : ℕ) (h1 : 1883 ≤ k) (h2 : k < 1884) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1883 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1883_ok
theorem cr_1882_1884 (k : ℕ) (h1 : 1882 ≤ k) (h2 : k < 1884) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1883 then cr_1882_1883 k h1 h else cr_1883_1884 k (by omega) h2
theorem cr_1881_1884 (k : ℕ) (h1 : 1881 ≤ k) (h2 : k < 1884) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1882 then cr_1881_1882 k h1 h else cr_1882_1884 k (by omega) h2
theorem cr_1884_1885 (k : ℕ) (h1 : 1884 ≤ k) (h2 : k < 1885) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1884 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1884_ok
theorem cr_1885_1886 (k : ℕ) (h1 : 1885 ≤ k) (h2 : k < 1886) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1885 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1885_ok
theorem cr_1886_1887 (k : ℕ) (h1 : 1886 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1886 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1886_ok
theorem cr_1885_1887 (k : ℕ) (h1 : 1885 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1886 then cr_1885_1886 k h1 h else cr_1886_1887 k (by omega) h2
theorem cr_1884_1887 (k : ℕ) (h1 : 1884 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1885 then cr_1884_1885 k h1 h else cr_1885_1887 k (by omega) h2
theorem cr_1881_1887 (k : ℕ) (h1 : 1881 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1884 then cr_1881_1884 k h1 h else cr_1884_1887 k (by omega) h2
theorem cr_1876_1887 (k : ℕ) (h1 : 1876 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1881 then cr_1876_1881 k h1 h else cr_1881_1887 k (by omega) h2
theorem cr_1866_1887 (k : ℕ) (h1 : 1866 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1876 then cr_1866_1876 k h1 h else cr_1876_1887 k (by omega) h2
theorem cr_1846_1887 (k : ℕ) (h1 : 1846 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1866 then cr_1846_1866 k h1 h else cr_1866_1887 k (by omega) h2
theorem cr_1805_1887 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1887) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1846 then cr_1805_1846 k h1 h else cr_1846_1887 k (by omega) h2
theorem cr_1887_1888 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1888) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1887 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1887_ok
theorem cr_1888_1889 (k : ℕ) (h1 : 1888 ≤ k) (h2 : k < 1889) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1888 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1888_ok
theorem cr_1887_1889 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1889) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1888 then cr_1887_1888 k h1 h else cr_1888_1889 k (by omega) h2
theorem cr_1889_1890 (k : ℕ) (h1 : 1889 ≤ k) (h2 : k < 1890) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1889 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1889_ok
theorem cr_1890_1891 (k : ℕ) (h1 : 1890 ≤ k) (h2 : k < 1891) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1890 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1890_ok
theorem cr_1891_1892 (k : ℕ) (h1 : 1891 ≤ k) (h2 : k < 1892) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1891 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1891_ok
theorem cr_1890_1892 (k : ℕ) (h1 : 1890 ≤ k) (h2 : k < 1892) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1891 then cr_1890_1891 k h1 h else cr_1891_1892 k (by omega) h2
theorem cr_1889_1892 (k : ℕ) (h1 : 1889 ≤ k) (h2 : k < 1892) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1890 then cr_1889_1890 k h1 h else cr_1890_1892 k (by omega) h2
theorem cr_1887_1892 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1892) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1889 then cr_1887_1889 k h1 h else cr_1889_1892 k (by omega) h2
theorem cr_1892_1893 (k : ℕ) (h1 : 1892 ≤ k) (h2 : k < 1893) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1892 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1892_ok
theorem cr_1893_1894 (k : ℕ) (h1 : 1893 ≤ k) (h2 : k < 1894) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1893 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1893_ok
theorem cr_1892_1894 (k : ℕ) (h1 : 1892 ≤ k) (h2 : k < 1894) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1893 then cr_1892_1893 k h1 h else cr_1893_1894 k (by omega) h2
theorem cr_1894_1895 (k : ℕ) (h1 : 1894 ≤ k) (h2 : k < 1895) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1894 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1894_ok
theorem cr_1895_1896 (k : ℕ) (h1 : 1895 ≤ k) (h2 : k < 1896) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1895 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1895_ok
theorem cr_1896_1897 (k : ℕ) (h1 : 1896 ≤ k) (h2 : k < 1897) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1896 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1896_ok
theorem cr_1895_1897 (k : ℕ) (h1 : 1895 ≤ k) (h2 : k < 1897) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1896 then cr_1895_1896 k h1 h else cr_1896_1897 k (by omega) h2
theorem cr_1894_1897 (k : ℕ) (h1 : 1894 ≤ k) (h2 : k < 1897) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1895 then cr_1894_1895 k h1 h else cr_1895_1897 k (by omega) h2
theorem cr_1892_1897 (k : ℕ) (h1 : 1892 ≤ k) (h2 : k < 1897) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1894 then cr_1892_1894 k h1 h else cr_1894_1897 k (by omega) h2
theorem cr_1887_1897 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1897) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1892 then cr_1887_1892 k h1 h else cr_1892_1897 k (by omega) h2
theorem cr_1897_1898 (k : ℕ) (h1 : 1897 ≤ k) (h2 : k < 1898) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1897 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1897_ok
theorem cr_1898_1899 (k : ℕ) (h1 : 1898 ≤ k) (h2 : k < 1899) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1898 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1898_ok
theorem cr_1897_1899 (k : ℕ) (h1 : 1897 ≤ k) (h2 : k < 1899) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1898 then cr_1897_1898 k h1 h else cr_1898_1899 k (by omega) h2
theorem cr_1899_1900 (k : ℕ) (h1 : 1899 ≤ k) (h2 : k < 1900) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1899 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1899_ok
theorem cr_1900_1901 (k : ℕ) (h1 : 1900 ≤ k) (h2 : k < 1901) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1900 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1900_ok
theorem cr_1901_1902 (k : ℕ) (h1 : 1901 ≤ k) (h2 : k < 1902) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1901 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1901_ok
theorem cr_1900_1902 (k : ℕ) (h1 : 1900 ≤ k) (h2 : k < 1902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1901 then cr_1900_1901 k h1 h else cr_1901_1902 k (by omega) h2
theorem cr_1899_1902 (k : ℕ) (h1 : 1899 ≤ k) (h2 : k < 1902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1900 then cr_1899_1900 k h1 h else cr_1900_1902 k (by omega) h2
theorem cr_1897_1902 (k : ℕ) (h1 : 1897 ≤ k) (h2 : k < 1902) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1899 then cr_1897_1899 k h1 h else cr_1899_1902 k (by omega) h2
theorem cr_1902_1903 (k : ℕ) (h1 : 1902 ≤ k) (h2 : k < 1903) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1902 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1902_ok
theorem cr_1903_1904 (k : ℕ) (h1 : 1903 ≤ k) (h2 : k < 1904) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1903 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1903_ok
theorem cr_1902_1904 (k : ℕ) (h1 : 1902 ≤ k) (h2 : k < 1904) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1903 then cr_1902_1903 k h1 h else cr_1903_1904 k (by omega) h2
theorem cr_1904_1905 (k : ℕ) (h1 : 1904 ≤ k) (h2 : k < 1905) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1904 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1904_ok
theorem cr_1905_1906 (k : ℕ) (h1 : 1905 ≤ k) (h2 : k < 1906) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1905 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1905_ok
theorem cr_1906_1907 (k : ℕ) (h1 : 1906 ≤ k) (h2 : k < 1907) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1906 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1906_ok
theorem cr_1905_1907 (k : ℕ) (h1 : 1905 ≤ k) (h2 : k < 1907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1906 then cr_1905_1906 k h1 h else cr_1906_1907 k (by omega) h2
theorem cr_1904_1907 (k : ℕ) (h1 : 1904 ≤ k) (h2 : k < 1907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1905 then cr_1904_1905 k h1 h else cr_1905_1907 k (by omega) h2
theorem cr_1902_1907 (k : ℕ) (h1 : 1902 ≤ k) (h2 : k < 1907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1904 then cr_1902_1904 k h1 h else cr_1904_1907 k (by omega) h2
theorem cr_1897_1907 (k : ℕ) (h1 : 1897 ≤ k) (h2 : k < 1907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1902 then cr_1897_1902 k h1 h else cr_1902_1907 k (by omega) h2
theorem cr_1887_1907 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1907) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1897 then cr_1887_1897 k h1 h else cr_1897_1907 k (by omega) h2
theorem cr_1907_1908 (k : ℕ) (h1 : 1907 ≤ k) (h2 : k < 1908) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1907 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1907_ok
theorem cr_1908_1909 (k : ℕ) (h1 : 1908 ≤ k) (h2 : k < 1909) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1908 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1908_ok
theorem cr_1907_1909 (k : ℕ) (h1 : 1907 ≤ k) (h2 : k < 1909) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1908 then cr_1907_1908 k h1 h else cr_1908_1909 k (by omega) h2
theorem cr_1909_1910 (k : ℕ) (h1 : 1909 ≤ k) (h2 : k < 1910) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1909 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1909_ok
theorem cr_1910_1911 (k : ℕ) (h1 : 1910 ≤ k) (h2 : k < 1911) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1910 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1910_ok
theorem cr_1911_1912 (k : ℕ) (h1 : 1911 ≤ k) (h2 : k < 1912) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1911 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1911_ok
theorem cr_1910_1912 (k : ℕ) (h1 : 1910 ≤ k) (h2 : k < 1912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1911 then cr_1910_1911 k h1 h else cr_1911_1912 k (by omega) h2
theorem cr_1909_1912 (k : ℕ) (h1 : 1909 ≤ k) (h2 : k < 1912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1910 then cr_1909_1910 k h1 h else cr_1910_1912 k (by omega) h2
theorem cr_1907_1912 (k : ℕ) (h1 : 1907 ≤ k) (h2 : k < 1912) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1909 then cr_1907_1909 k h1 h else cr_1909_1912 k (by omega) h2
theorem cr_1912_1913 (k : ℕ) (h1 : 1912 ≤ k) (h2 : k < 1913) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1912 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1912_ok
theorem cr_1913_1914 (k : ℕ) (h1 : 1913 ≤ k) (h2 : k < 1914) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1913 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1913_ok
theorem cr_1912_1914 (k : ℕ) (h1 : 1912 ≤ k) (h2 : k < 1914) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1913 then cr_1912_1913 k h1 h else cr_1913_1914 k (by omega) h2
theorem cr_1914_1915 (k : ℕ) (h1 : 1914 ≤ k) (h2 : k < 1915) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1914 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1914_ok
theorem cr_1915_1916 (k : ℕ) (h1 : 1915 ≤ k) (h2 : k < 1916) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1915 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1915_ok
theorem cr_1916_1917 (k : ℕ) (h1 : 1916 ≤ k) (h2 : k < 1917) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1916 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1916_ok
theorem cr_1915_1917 (k : ℕ) (h1 : 1915 ≤ k) (h2 : k < 1917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1916 then cr_1915_1916 k h1 h else cr_1916_1917 k (by omega) h2
theorem cr_1914_1917 (k : ℕ) (h1 : 1914 ≤ k) (h2 : k < 1917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1915 then cr_1914_1915 k h1 h else cr_1915_1917 k (by omega) h2
theorem cr_1912_1917 (k : ℕ) (h1 : 1912 ≤ k) (h2 : k < 1917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1914 then cr_1912_1914 k h1 h else cr_1914_1917 k (by omega) h2
theorem cr_1907_1917 (k : ℕ) (h1 : 1907 ≤ k) (h2 : k < 1917) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1912 then cr_1907_1912 k h1 h else cr_1912_1917 k (by omega) h2
theorem cr_1917_1918 (k : ℕ) (h1 : 1917 ≤ k) (h2 : k < 1918) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1917 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1917_ok
theorem cr_1918_1919 (k : ℕ) (h1 : 1918 ≤ k) (h2 : k < 1919) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1918 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1918_ok
theorem cr_1917_1919 (k : ℕ) (h1 : 1917 ≤ k) (h2 : k < 1919) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1918 then cr_1917_1918 k h1 h else cr_1918_1919 k (by omega) h2
theorem cr_1919_1920 (k : ℕ) (h1 : 1919 ≤ k) (h2 : k < 1920) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1919 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1919_ok
theorem cr_1920_1921 (k : ℕ) (h1 : 1920 ≤ k) (h2 : k < 1921) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1920 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1920_ok
theorem cr_1921_1922 (k : ℕ) (h1 : 1921 ≤ k) (h2 : k < 1922) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1921 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1921_ok
theorem cr_1920_1922 (k : ℕ) (h1 : 1920 ≤ k) (h2 : k < 1922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1921 then cr_1920_1921 k h1 h else cr_1921_1922 k (by omega) h2
theorem cr_1919_1922 (k : ℕ) (h1 : 1919 ≤ k) (h2 : k < 1922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1920 then cr_1919_1920 k h1 h else cr_1920_1922 k (by omega) h2
theorem cr_1917_1922 (k : ℕ) (h1 : 1917 ≤ k) (h2 : k < 1922) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1919 then cr_1917_1919 k h1 h else cr_1919_1922 k (by omega) h2
theorem cr_1922_1923 (k : ℕ) (h1 : 1922 ≤ k) (h2 : k < 1923) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1922 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1922_ok
theorem cr_1923_1924 (k : ℕ) (h1 : 1923 ≤ k) (h2 : k < 1924) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1923 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1923_ok
theorem cr_1924_1925 (k : ℕ) (h1 : 1924 ≤ k) (h2 : k < 1925) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1924 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1924_ok
theorem cr_1923_1925 (k : ℕ) (h1 : 1923 ≤ k) (h2 : k < 1925) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1924 then cr_1923_1924 k h1 h else cr_1924_1925 k (by omega) h2
theorem cr_1922_1925 (k : ℕ) (h1 : 1922 ≤ k) (h2 : k < 1925) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1923 then cr_1922_1923 k h1 h else cr_1923_1925 k (by omega) h2
theorem cr_1925_1926 (k : ℕ) (h1 : 1925 ≤ k) (h2 : k < 1926) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1925 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1925_ok
theorem cr_1926_1927 (k : ℕ) (h1 : 1926 ≤ k) (h2 : k < 1927) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1926 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1926_ok
theorem cr_1927_1928 (k : ℕ) (h1 : 1927 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1927 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1927_ok
theorem cr_1926_1928 (k : ℕ) (h1 : 1926 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1927 then cr_1926_1927 k h1 h else cr_1927_1928 k (by omega) h2
theorem cr_1925_1928 (k : ℕ) (h1 : 1925 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1926 then cr_1925_1926 k h1 h else cr_1926_1928 k (by omega) h2
theorem cr_1922_1928 (k : ℕ) (h1 : 1922 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1925 then cr_1922_1925 k h1 h else cr_1925_1928 k (by omega) h2
theorem cr_1917_1928 (k : ℕ) (h1 : 1917 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1922 then cr_1917_1922 k h1 h else cr_1922_1928 k (by omega) h2
theorem cr_1907_1928 (k : ℕ) (h1 : 1907 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1917 then cr_1907_1917 k h1 h else cr_1917_1928 k (by omega) h2
theorem cr_1887_1928 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1928) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1907 then cr_1887_1907 k h1 h else cr_1907_1928 k (by omega) h2
theorem cr_1928_1929 (k : ℕ) (h1 : 1928 ≤ k) (h2 : k < 1929) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1928 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1928_ok
theorem cr_1929_1930 (k : ℕ) (h1 : 1929 ≤ k) (h2 : k < 1930) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1929 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1929_ok
theorem cr_1928_1930 (k : ℕ) (h1 : 1928 ≤ k) (h2 : k < 1930) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1929 then cr_1928_1929 k h1 h else cr_1929_1930 k (by omega) h2
theorem cr_1930_1931 (k : ℕ) (h1 : 1930 ≤ k) (h2 : k < 1931) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1930 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1930_ok
theorem cr_1931_1932 (k : ℕ) (h1 : 1931 ≤ k) (h2 : k < 1932) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1931 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1931_ok
theorem cr_1932_1933 (k : ℕ) (h1 : 1932 ≤ k) (h2 : k < 1933) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1932 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1932_ok
theorem cr_1931_1933 (k : ℕ) (h1 : 1931 ≤ k) (h2 : k < 1933) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1932 then cr_1931_1932 k h1 h else cr_1932_1933 k (by omega) h2
theorem cr_1930_1933 (k : ℕ) (h1 : 1930 ≤ k) (h2 : k < 1933) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1931 then cr_1930_1931 k h1 h else cr_1931_1933 k (by omega) h2
theorem cr_1928_1933 (k : ℕ) (h1 : 1928 ≤ k) (h2 : k < 1933) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1930 then cr_1928_1930 k h1 h else cr_1930_1933 k (by omega) h2
theorem cr_1933_1934 (k : ℕ) (h1 : 1933 ≤ k) (h2 : k < 1934) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1933 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1933_ok
theorem cr_1934_1935 (k : ℕ) (h1 : 1934 ≤ k) (h2 : k < 1935) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1934 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1934_ok
theorem cr_1933_1935 (k : ℕ) (h1 : 1933 ≤ k) (h2 : k < 1935) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1934 then cr_1933_1934 k h1 h else cr_1934_1935 k (by omega) h2
theorem cr_1935_1936 (k : ℕ) (h1 : 1935 ≤ k) (h2 : k < 1936) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1935 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1935_ok
theorem cr_1936_1937 (k : ℕ) (h1 : 1936 ≤ k) (h2 : k < 1937) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1936 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1936_ok
theorem cr_1937_1938 (k : ℕ) (h1 : 1937 ≤ k) (h2 : k < 1938) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1937 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1937_ok
theorem cr_1936_1938 (k : ℕ) (h1 : 1936 ≤ k) (h2 : k < 1938) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1937 then cr_1936_1937 k h1 h else cr_1937_1938 k (by omega) h2
theorem cr_1935_1938 (k : ℕ) (h1 : 1935 ≤ k) (h2 : k < 1938) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1936 then cr_1935_1936 k h1 h else cr_1936_1938 k (by omega) h2
theorem cr_1933_1938 (k : ℕ) (h1 : 1933 ≤ k) (h2 : k < 1938) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1935 then cr_1933_1935 k h1 h else cr_1935_1938 k (by omega) h2
theorem cr_1928_1938 (k : ℕ) (h1 : 1928 ≤ k) (h2 : k < 1938) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1933 then cr_1928_1933 k h1 h else cr_1933_1938 k (by omega) h2
theorem cr_1938_1939 (k : ℕ) (h1 : 1938 ≤ k) (h2 : k < 1939) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1938 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1938_ok
theorem cr_1939_1940 (k : ℕ) (h1 : 1939 ≤ k) (h2 : k < 1940) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1939 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1939_ok
theorem cr_1938_1940 (k : ℕ) (h1 : 1938 ≤ k) (h2 : k < 1940) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1939 then cr_1938_1939 k h1 h else cr_1939_1940 k (by omega) h2
theorem cr_1940_1941 (k : ℕ) (h1 : 1940 ≤ k) (h2 : k < 1941) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1940 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1940_ok
theorem cr_1941_1942 (k : ℕ) (h1 : 1941 ≤ k) (h2 : k < 1942) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1941 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1941_ok
theorem cr_1942_1943 (k : ℕ) (h1 : 1942 ≤ k) (h2 : k < 1943) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1942 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1942_ok
theorem cr_1941_1943 (k : ℕ) (h1 : 1941 ≤ k) (h2 : k < 1943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1942 then cr_1941_1942 k h1 h else cr_1942_1943 k (by omega) h2
theorem cr_1940_1943 (k : ℕ) (h1 : 1940 ≤ k) (h2 : k < 1943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1941 then cr_1940_1941 k h1 h else cr_1941_1943 k (by omega) h2
theorem cr_1938_1943 (k : ℕ) (h1 : 1938 ≤ k) (h2 : k < 1943) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1940 then cr_1938_1940 k h1 h else cr_1940_1943 k (by omega) h2
theorem cr_1943_1944 (k : ℕ) (h1 : 1943 ≤ k) (h2 : k < 1944) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1943 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1943_ok
theorem cr_1944_1945 (k : ℕ) (h1 : 1944 ≤ k) (h2 : k < 1945) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1944 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1944_ok
theorem cr_1945_1946 (k : ℕ) (h1 : 1945 ≤ k) (h2 : k < 1946) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1945 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1945_ok
theorem cr_1944_1946 (k : ℕ) (h1 : 1944 ≤ k) (h2 : k < 1946) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1945 then cr_1944_1945 k h1 h else cr_1945_1946 k (by omega) h2
theorem cr_1943_1946 (k : ℕ) (h1 : 1943 ≤ k) (h2 : k < 1946) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1944 then cr_1943_1944 k h1 h else cr_1944_1946 k (by omega) h2
theorem cr_1946_1947 (k : ℕ) (h1 : 1946 ≤ k) (h2 : k < 1947) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1946 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1946_ok
theorem cr_1947_1948 (k : ℕ) (h1 : 1947 ≤ k) (h2 : k < 1948) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1947 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1947_ok
theorem cr_1948_1949 (k : ℕ) (h1 : 1948 ≤ k) (h2 : k < 1949) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1948 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1948_ok
theorem cr_1947_1949 (k : ℕ) (h1 : 1947 ≤ k) (h2 : k < 1949) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1948 then cr_1947_1948 k h1 h else cr_1948_1949 k (by omega) h2
theorem cr_1946_1949 (k : ℕ) (h1 : 1946 ≤ k) (h2 : k < 1949) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1947 then cr_1946_1947 k h1 h else cr_1947_1949 k (by omega) h2
theorem cr_1943_1949 (k : ℕ) (h1 : 1943 ≤ k) (h2 : k < 1949) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1946 then cr_1943_1946 k h1 h else cr_1946_1949 k (by omega) h2
theorem cr_1938_1949 (k : ℕ) (h1 : 1938 ≤ k) (h2 : k < 1949) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1943 then cr_1938_1943 k h1 h else cr_1943_1949 k (by omega) h2
theorem cr_1928_1949 (k : ℕ) (h1 : 1928 ≤ k) (h2 : k < 1949) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1938 then cr_1928_1938 k h1 h else cr_1938_1949 k (by omega) h2
theorem cr_1949_1950 (k : ℕ) (h1 : 1949 ≤ k) (h2 : k < 1950) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1949 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1949_ok
theorem cr_1950_1951 (k : ℕ) (h1 : 1950 ≤ k) (h2 : k < 1951) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1950 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1950_ok
theorem cr_1949_1951 (k : ℕ) (h1 : 1949 ≤ k) (h2 : k < 1951) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1950 then cr_1949_1950 k h1 h else cr_1950_1951 k (by omega) h2
theorem cr_1951_1952 (k : ℕ) (h1 : 1951 ≤ k) (h2 : k < 1952) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1951 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1951_ok
theorem cr_1952_1953 (k : ℕ) (h1 : 1952 ≤ k) (h2 : k < 1953) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1952 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1952_ok
theorem cr_1953_1954 (k : ℕ) (h1 : 1953 ≤ k) (h2 : k < 1954) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1953 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1953_ok
theorem cr_1952_1954 (k : ℕ) (h1 : 1952 ≤ k) (h2 : k < 1954) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1953 then cr_1952_1953 k h1 h else cr_1953_1954 k (by omega) h2
theorem cr_1951_1954 (k : ℕ) (h1 : 1951 ≤ k) (h2 : k < 1954) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1952 then cr_1951_1952 k h1 h else cr_1952_1954 k (by omega) h2
theorem cr_1949_1954 (k : ℕ) (h1 : 1949 ≤ k) (h2 : k < 1954) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1951 then cr_1949_1951 k h1 h else cr_1951_1954 k (by omega) h2
theorem cr_1954_1955 (k : ℕ) (h1 : 1954 ≤ k) (h2 : k < 1955) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1954 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1954_ok
theorem cr_1955_1956 (k : ℕ) (h1 : 1955 ≤ k) (h2 : k < 1956) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1955 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1955_ok
theorem cr_1954_1956 (k : ℕ) (h1 : 1954 ≤ k) (h2 : k < 1956) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1955 then cr_1954_1955 k h1 h else cr_1955_1956 k (by omega) h2
theorem cr_1956_1957 (k : ℕ) (h1 : 1956 ≤ k) (h2 : k < 1957) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1956 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1956_ok
theorem cr_1957_1958 (k : ℕ) (h1 : 1957 ≤ k) (h2 : k < 1958) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1957 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1957_ok
theorem cr_1958_1959 (k : ℕ) (h1 : 1958 ≤ k) (h2 : k < 1959) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1958 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1958_ok
theorem cr_1957_1959 (k : ℕ) (h1 : 1957 ≤ k) (h2 : k < 1959) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1958 then cr_1957_1958 k h1 h else cr_1958_1959 k (by omega) h2
theorem cr_1956_1959 (k : ℕ) (h1 : 1956 ≤ k) (h2 : k < 1959) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1957 then cr_1956_1957 k h1 h else cr_1957_1959 k (by omega) h2
theorem cr_1954_1959 (k : ℕ) (h1 : 1954 ≤ k) (h2 : k < 1959) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1956 then cr_1954_1956 k h1 h else cr_1956_1959 k (by omega) h2
theorem cr_1949_1959 (k : ℕ) (h1 : 1949 ≤ k) (h2 : k < 1959) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1954 then cr_1949_1954 k h1 h else cr_1954_1959 k (by omega) h2
theorem cr_1959_1960 (k : ℕ) (h1 : 1959 ≤ k) (h2 : k < 1960) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1959 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1959_ok
theorem cr_1960_1961 (k : ℕ) (h1 : 1960 ≤ k) (h2 : k < 1961) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1960 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1960_ok
theorem cr_1959_1961 (k : ℕ) (h1 : 1959 ≤ k) (h2 : k < 1961) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1960 then cr_1959_1960 k h1 h else cr_1960_1961 k (by omega) h2
theorem cr_1961_1962 (k : ℕ) (h1 : 1961 ≤ k) (h2 : k < 1962) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1961 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1961_ok
theorem cr_1962_1963 (k : ℕ) (h1 : 1962 ≤ k) (h2 : k < 1963) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1962 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1962_ok
theorem cr_1963_1964 (k : ℕ) (h1 : 1963 ≤ k) (h2 : k < 1964) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1963 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1963_ok
theorem cr_1962_1964 (k : ℕ) (h1 : 1962 ≤ k) (h2 : k < 1964) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1963 then cr_1962_1963 k h1 h else cr_1963_1964 k (by omega) h2
theorem cr_1961_1964 (k : ℕ) (h1 : 1961 ≤ k) (h2 : k < 1964) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1962 then cr_1961_1962 k h1 h else cr_1962_1964 k (by omega) h2
theorem cr_1959_1964 (k : ℕ) (h1 : 1959 ≤ k) (h2 : k < 1964) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1961 then cr_1959_1961 k h1 h else cr_1961_1964 k (by omega) h2
theorem cr_1964_1965 (k : ℕ) (h1 : 1964 ≤ k) (h2 : k < 1965) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1964 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1964_ok
theorem cr_1965_1966 (k : ℕ) (h1 : 1965 ≤ k) (h2 : k < 1966) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1965 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1965_ok
theorem cr_1966_1967 (k : ℕ) (h1 : 1966 ≤ k) (h2 : k < 1967) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1966 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1966_ok
theorem cr_1965_1967 (k : ℕ) (h1 : 1965 ≤ k) (h2 : k < 1967) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1966 then cr_1965_1966 k h1 h else cr_1966_1967 k (by omega) h2
theorem cr_1964_1967 (k : ℕ) (h1 : 1964 ≤ k) (h2 : k < 1967) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1965 then cr_1964_1965 k h1 h else cr_1965_1967 k (by omega) h2
theorem cr_1967_1968 (k : ℕ) (h1 : 1967 ≤ k) (h2 : k < 1968) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1967 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1967_ok
theorem cr_1968_1969 (k : ℕ) (h1 : 1968 ≤ k) (h2 : k < 1969) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1968 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1968_ok
theorem cr_1969_1970 (k : ℕ) (h1 : 1969 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1969 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1969_ok
theorem cr_1968_1970 (k : ℕ) (h1 : 1968 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1969 then cr_1968_1969 k h1 h else cr_1969_1970 k (by omega) h2
theorem cr_1967_1970 (k : ℕ) (h1 : 1967 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1968 then cr_1967_1968 k h1 h else cr_1968_1970 k (by omega) h2
theorem cr_1964_1970 (k : ℕ) (h1 : 1964 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1967 then cr_1964_1967 k h1 h else cr_1967_1970 k (by omega) h2
theorem cr_1959_1970 (k : ℕ) (h1 : 1959 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1964 then cr_1959_1964 k h1 h else cr_1964_1970 k (by omega) h2
theorem cr_1949_1970 (k : ℕ) (h1 : 1949 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1959 then cr_1949_1959 k h1 h else cr_1959_1970 k (by omega) h2
theorem cr_1928_1970 (k : ℕ) (h1 : 1928 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1949 then cr_1928_1949 k h1 h else cr_1949_1970 k (by omega) h2
theorem cr_1887_1970 (k : ℕ) (h1 : 1887 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1928 then cr_1887_1928 k h1 h else cr_1928_1970 k (by omega) h2
theorem cr_1805_1970 (k : ℕ) (h1 : 1805 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1887 then cr_1805_1887 k h1 h else cr_1887_1970 k (by omega) h2
theorem cr_1641_1970 (k : ℕ) (h1 : 1641 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1805 then cr_1641_1805 k h1 h else cr_1805_1970 k (by omega) h2
theorem cr_1313_1970 (k : ℕ) (h1 : 1313 ≤ k) (h2 : k < 1970) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1641 then cr_1313_1641 k h1 h else cr_1641_1970 k (by omega) h2

end Harris
