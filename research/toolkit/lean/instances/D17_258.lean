import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 258 of the cap-17 certificate: slots 132096 .. 132607 -/
theorem chk_258 : chunkCheck 17 T stdSt 132096 512 = true := by decide +kernel

end Row17
