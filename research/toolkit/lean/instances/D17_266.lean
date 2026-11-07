import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 266 of the cap-17 certificate: slots 136192 .. 136703 -/
theorem chk_266 : chunkCheck 17 T stdSt 136192 512 = true := by decide +kernel

end Row17
