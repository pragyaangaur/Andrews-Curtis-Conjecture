import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 259 of the cap-17 certificate: slots 132608 .. 133119 -/
theorem chk_259 : chunkCheck 17 T stdSt 132608 512 = true := by decide +kernel

end Row17
