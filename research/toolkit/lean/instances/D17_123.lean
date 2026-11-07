import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 123 of the cap-17 certificate: slots 62976 .. 63487 -/
theorem chk_123 : chunkCheck 17 T stdSt 62976 512 = true := by decide +kernel

end Row17
