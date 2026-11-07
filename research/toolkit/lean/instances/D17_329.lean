import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 329 of the cap-17 certificate: slots 168448 .. 168959 -/
theorem chk_329 : chunkCheck 17 T stdSt 168448 512 = true := by decide +kernel

end Row17
