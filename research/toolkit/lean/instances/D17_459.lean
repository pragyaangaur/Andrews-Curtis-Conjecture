import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 459 of the cap-17 certificate: slots 235008 .. 235519 -/
theorem chk_459 : chunkCheck 17 T stdSt 235008 512 = true := by decide +kernel

end Row17
