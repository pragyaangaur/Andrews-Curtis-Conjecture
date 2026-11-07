import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 31 of the cap-17 certificate: slots 15872 .. 16383 -/
theorem chk_31 : chunkCheck 17 T stdSt 15872 512 = true := by decide +kernel

end Row17
