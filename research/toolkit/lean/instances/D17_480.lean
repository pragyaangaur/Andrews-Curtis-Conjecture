import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 480 of the cap-17 certificate: slots 245760 .. 246271 -/
theorem chk_480 : chunkCheck 17 T stdSt 245760 512 = true := by decide +kernel

end Row17
