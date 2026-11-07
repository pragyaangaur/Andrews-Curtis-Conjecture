import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 498 of the cap-17 certificate: slots 254976 .. 255487 -/
theorem chk_498 : chunkCheck 17 T stdSt 254976 512 = true := by decide +kernel

end Row17
