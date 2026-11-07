import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 205 of the cap-17 certificate: slots 104960 .. 105471 -/
theorem chk_205 : chunkCheck 17 T stdSt 104960 512 = true := by decide +kernel

end Row17
