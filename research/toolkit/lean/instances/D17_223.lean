import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 223 of the cap-17 certificate: slots 114176 .. 114687 -/
theorem chk_223 : chunkCheck 17 T stdSt 114176 512 = true := by decide +kernel

end Row17
