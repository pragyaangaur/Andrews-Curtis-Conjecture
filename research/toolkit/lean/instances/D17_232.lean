import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 232 of the cap-17 certificate: slots 118784 .. 119295 -/
theorem chk_232 : chunkCheck 17 T stdSt 118784 512 = true := by decide +kernel

end Row17
