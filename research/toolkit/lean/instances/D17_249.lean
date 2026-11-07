import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 249 of the cap-17 certificate: slots 127488 .. 127999 -/
theorem chk_249 : chunkCheck 17 T stdSt 127488 512 = true := by decide +kernel

end Row17
