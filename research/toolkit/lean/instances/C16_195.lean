import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 195 of the cap-16 certificate: slots 199680 .. 200703 -/
theorem chk_195 : chunkCheck 16 T stdSt 199680 1024 = true := by decide +kernel

end Row16
