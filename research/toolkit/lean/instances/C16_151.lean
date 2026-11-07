import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 151 of the cap-16 certificate: slots 154624 .. 155647 -/
theorem chk_151 : chunkCheck 16 T stdSt 154624 1024 = true := by decide +kernel

end Row16
