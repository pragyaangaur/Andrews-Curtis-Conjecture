import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 228 of the cap-17 certificate: slots 116736 .. 117247 -/
theorem chk_228 : chunkCheck 17 T stdSt 116736 512 = true := by decide +kernel

end Row17
