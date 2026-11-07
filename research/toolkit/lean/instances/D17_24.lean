import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 24 of the cap-17 certificate: slots 12288 .. 12799 -/
theorem chk_24 : chunkCheck 17 T stdSt 12288 512 = true := by decide +kernel

end Row17
