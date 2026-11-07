import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 141 of the cap-17 certificate: slots 72192 .. 72703 -/
theorem chk_141 : chunkCheck 17 T stdSt 72192 512 = true := by decide +kernel

end Row17
