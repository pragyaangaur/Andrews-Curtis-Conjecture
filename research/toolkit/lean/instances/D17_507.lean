import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 507 of the cap-17 certificate: slots 259584 .. 260095 -/
theorem chk_507 : chunkCheck 17 T stdSt 259584 512 = true := by decide +kernel

end Row17
