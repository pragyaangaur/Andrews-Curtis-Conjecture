import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 154 of the cap-16 certificate: slots 157696 .. 158719 -/
theorem chk_154 : chunkCheck 16 T stdSt 157696 1024 = true := by decide +kernel

end Row16
