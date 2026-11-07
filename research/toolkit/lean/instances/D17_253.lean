import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 253 of the cap-17 certificate: slots 129536 .. 130047 -/
theorem chk_253 : chunkCheck 17 T stdSt 129536 512 = true := by decide +kernel

end Row17
