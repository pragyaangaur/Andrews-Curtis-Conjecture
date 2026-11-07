import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 391 of the cap-17 certificate: slots 200192 .. 200703 -/
theorem chk_391 : chunkCheck 17 T stdSt 200192 512 = true := by decide +kernel

end Row17
