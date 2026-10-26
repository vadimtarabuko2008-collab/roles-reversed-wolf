import * as THREE from 'three';
import './style.css';

type Phase = 'День' | 'Сумерки' | 'Ночь' | 'Рассвет';

interface Sheep {
  mesh: THREE.Group;
  velocity: THREE.Vector3;
  alive: boolean;
  turnIn: number;
}

const MAP_W = 32;
const MAP_H = 24;
const GOAL = 4;
const START_HEALTH = 6;
const CHANGE_TIME = 3;
const CYCLE_TIME = 120;

const ui = {
  phase: required('phase'),
  time: required('time'),
  sheep: required('sheep'),
  health: required('health'),
  form: required('form'),
  danger: required('danger'),
  hint: required('hint'),
  progress: required('change-progress'),
  sound: requiredButton('sound'),
  overlay: required('overlay'),
  overlayTitle: required('overlay-title'),
  overlayText: required('overlay-text'),
  start: requiredButton('start'),
};

function required(id: string): HTMLElement {
  const element = document.getElementById(id);
  if (!element) throw new Error(`Missing element #${id}`);
  return element;
}

function requiredButton(id: string): HTMLButtonElement {
  const element = required(id);
  if (!(element instanceof HTMLButtonElement)) throw new Error(`#${id} is not a button`);
  return element;
}

class PrototypeGame {
  private readonly scene = new THREE.Scene();
  private readonly camera: THREE.OrthographicCamera;
  private readonly renderer = new THREE.WebGLRenderer({ antialias: true });
  private readonly clock = new THREE.Clock();
  private readonly keys = new Set<string>();
  private readonly sheep: Sheep[] = [];
  private readonly wolf = this.createWolf();
  private readonly dog = this.createDog();
  private readonly sun = new THREE.DirectionalLight(0xffedc7, 2.1);
  private readonly sky = new THREE.HemisphereLight(0xc7e9ff, 0x344223, 1.6);
  private readonly cameraTarget = new THREE.Vector3();

  private running = false;
  private finished = false;
  private disguised = true;
  private elapsed = 0;
  private changeProgress = 0;
  private score = 0;
  private health = START_HEALTH;
  private maxHealth = START_HEALTH;
  private biteCooldown = 0;
  private actionCooldown = 0;
  private phase: Phase = 'День';
  private audioContext?: AudioContext;
  private soundEnabled = true;

  constructor(container: HTMLElement) {
    const aspect = window.innerWidth / window.innerHeight;
    const view = 18;
    this.camera = new THREE.OrthographicCamera(-view * aspect, view * aspect, view, -view, 0.1, 100);
    this.camera.position.set(18, 23, 18);
    this.camera.lookAt(0, 0, 0);

    this.renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
    this.renderer.setSize(window.innerWidth, window.innerHeight);
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    container.appendChild(this.renderer.domElement);

    this.buildWorld();
    this.bindEvents();
    this.reset();
    this.renderer.setAnimationLoop(() => this.frame());
  }

  start(): void {
    this.ensureAudio();
    this.playTone(392, .1, .05);
    window.setTimeout(() => this.playTone(523, .13, .04), 90);
    this.reset();
    this.running = true;
    ui.overlay.classList.add('hidden');
    this.clock.start();
  }

  private reset(): void {
    this.finished = false;
    this.running = false;
    this.elapsed = 0;
    this.score = 0;
    this.health = START_HEALTH;
    this.maxHealth = START_HEALTH;
    this.disguised = true;
    this.changeProgress = 0;
    this.biteCooldown = 0;
    this.actionCooldown = 0;
    this.wolf.position.set(0, 0, 5);
    this.dog.position.set(-10, 0, -7);
    this.setDisguiseVisual();
    this.resetSheep();
    this.updateUi();
  }

  private buildWorld(): void {
    this.scene.background = new THREE.Color(0xaacb8b);
    this.scene.fog = new THREE.Fog(0xaacb8b, 25, 52);

    const ground = new THREE.Mesh(
      new THREE.PlaneGeometry(MAP_W, MAP_H),
      new THREE.MeshStandardMaterial({ color: 0x64814e, roughness: 1 }),
    );
    ground.rotation.x = -Math.PI / 2;
    ground.receiveShadow = true;
    this.scene.add(ground);

    this.sun.position.set(10, 20, 8);
    this.sun.castShadow = true;
    this.sun.shadow.mapSize.set(1024, 1024);
    this.scene.add(this.sun, this.sky);

    this.scene.add(this.wolf, this.dog);
    for (let i = 0; i < 8; i += 1) {
      const sheep = { mesh: this.createSheep(), velocity: new THREE.Vector3(), alive: true, turnIn: 0 };
      this.sheep.push(sheep);
      this.scene.add(sheep.mesh);
    }

    const fenceMaterial = new THREE.MeshStandardMaterial({ color: 0x765333, roughness: 1 });
    const addFence = (x: number, z: number, sx: number, sz: number) => {
      const fence = new THREE.Mesh(new THREE.BoxGeometry(sx, 0.8, sz), fenceMaterial);
      fence.position.set(x, 0.4, z);
      fence.castShadow = true;
      this.scene.add(fence);
    };
    addFence(0, -MAP_H / 2, MAP_W + 1, 0.28);
    addFence(0, MAP_H / 2, MAP_W + 1, 0.28);
    addFence(-MAP_W / 2, 0, 0.28, MAP_H + 1);
    addFence(MAP_W / 2, 0, 0.28, MAP_H + 1);

    const barn = new THREE.Mesh(
      new THREE.BoxGeometry(5, 3.5, 4),
      new THREE.MeshStandardMaterial({ color: 0x763f32, roughness: .9 }),
    );
    barn.position.set(11, 1.75, -8);
    barn.castShadow = true;
    barn.receiveShadow = true;
    this.scene.add(barn);

    for (let i = 0; i < 34; i += 1) {
      const tuft = new THREE.Mesh(
        new THREE.ConeGeometry(.08 + Math.random() * .08, .35 + Math.random() * .3, 4),
        new THREE.MeshStandardMaterial({ color: i % 3 === 0 ? 0x8ba964 : 0x759653 }),
      );
      tuft.position.set(random(-15, 15), .2, random(-11, 11));
      this.scene.add(tuft);
    }
  }

  private createWolf(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'wolf';
    const dark = new THREE.MeshStandardMaterial({ color: 0x3f4448, roughness: .75 });
    const wool = new THREE.MeshStandardMaterial({ color: 0xe8e1ca, roughness: 1 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.62, 1.05, 5, 10), dark);
    body.rotation.z = Math.PI / 2;
    body.position.y = .78;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.ConeGeometry(.55, 1.25, 7), dark);
    head.rotation.z = -Math.PI / 2;
    head.position.set(.95, .95, 0);
    head.castShadow = true;
    const coat = new THREE.Mesh(new THREE.SphereGeometry(.9, 12, 8), wool);
    coat.name = 'coat';
    coat.scale.set(1.15, .85, .85);
    coat.position.y = .82;
    coat.castShadow = true;
    group.add(body, head, coat);
    return group;
  }

  private createSheep(): THREE.Group {
    const group = new THREE.Group();
    const wool = new THREE.MeshStandardMaterial({ color: 0xf3ead4, roughness: 1 });
    const face = new THREE.MeshStandardMaterial({ color: 0x38342f, roughness: 1 });
    const body = new THREE.Mesh(new THREE.SphereGeometry(.68, 10, 8), wool);
    body.scale.set(1.25, .9, .82);
    body.position.y = .72;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.BoxGeometry(.42, .5, .45), face);
    head.position.set(.78, .72, 0);
    head.castShadow = true;
    group.add(body, head);
    return group;
  }

  private createDog(): THREE.Group {
    const group = new THREE.Group();
    const material = new THREE.MeshStandardMaterial({ color: 0x7a4f31, roughness: .8 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.58, 1.15, 5, 9), material);
    body.rotation.z = Math.PI / 2;
    body.position.y = .68;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.BoxGeometry(.75, .72, .7), material);
    head.position.set(.95, .87, 0);
    head.castShadow = true;
    group.add(body, head);
    return group;
  }

  private bindEvents(): void {
    window.addEventListener('keydown', (event) => {
      this.keys.add(event.code);
      if (event.code === 'Space') event.preventDefault();
      if (event.code === 'KeyR' && this.finished) this.showIntro();
    });
    window.addEventListener('keyup', (event) => this.keys.delete(event.code));
    window.addEventListener('blur', () => this.keys.clear());
    window.addEventListener('resize', () => this.resize());
    ui.start.addEventListener('click', () => this.start());
    ui.sound.addEventListener('click', () => {
      this.soundEnabled = !this.soundEnabled;
      ui.sound.textContent = `Звук: ${this.soundEnabled ? 'вкл' : 'выкл'}`;
      ui.sound.setAttribute('aria-pressed', String(this.soundEnabled));
      if (this.soundEnabled) {
        this.ensureAudio();
        this.playTone(520, .08, .035);
      }
    });
  }

  private frame(): void {
    const dt = Math.min(this.clock.getDelta(), .05);
    if (this.running) this.update(dt);
    this.renderer.render(this.scene, this.camera);
  }

  private update(dt: number): void {
    this.elapsed += dt;
    this.biteCooldown = Math.max(0, this.biteCooldown - dt);
    this.actionCooldown = Math.max(0, this.actionCooldown - dt);
    const moved = this.updatePlayer(dt);
    this.updateDisguise(dt, moved);
    this.updateSheep(dt);
    this.updateDog(dt);
    this.updatePhase();
    this.tryEatSheep();
    this.updateCamera(dt);
    this.updateUi();
  }

  private updatePlayer(dt: number): boolean {
    const input = new THREE.Vector3(
      Number(this.keys.has('KeyD') || this.keys.has('ArrowRight')) - Number(this.keys.has('KeyA') || this.keys.has('ArrowLeft')),
      0,
      Number(this.keys.has('KeyS') || this.keys.has('ArrowDown')) - Number(this.keys.has('KeyW') || this.keys.has('ArrowUp')),
    );
    if (input.lengthSq() === 0) return false;
    input.normalize();
    const speed = this.disguised ? 3.4 : 4.5;
    this.wolf.position.addScaledVector(input, speed * dt);
    this.wolf.position.x = THREE.MathUtils.clamp(this.wolf.position.x, -MAP_W / 2 + 1, MAP_W / 2 - 1);
    this.wolf.position.z = THREE.MathUtils.clamp(this.wolf.position.z, -MAP_H / 2 + 1, MAP_H / 2 - 1);
    this.wolf.rotation.y = Math.atan2(-input.z, input.x);
    return true;
  }

  private updateDisguise(dt: number, moved: boolean): void {
    if (!this.keys.has('KeyF')) {
      this.changeProgress = 0;
      return;
    }
    if (moved) {
      this.changeProgress = 0;
      ui.hint.textContent = 'Чтобы переодеться, стойте неподвижно';
      return;
    }
    this.changeProgress += dt;
    if (this.changeProgress >= CHANGE_TIME) {
      this.disguised = !this.disguised;
      this.changeProgress = 0;
      this.keys.delete('KeyF');
      this.setDisguiseVisual();
      this.playTone(this.disguised ? 620 : 310, .12, .035);
    }
  }

  private setDisguiseVisual(): void {
    const coat = this.wolf.getObjectByName('coat');
    if (coat) coat.visible = this.disguised;
  }

  private updateSheep(dt: number): void {
    for (const sheep of this.sheep) {
      if (!sheep.alive) continue;
      sheep.turnIn -= dt;
      const wolfDistance = sheep.mesh.position.distanceTo(this.wolf.position);
      if (!this.disguised && wolfDistance < 5) {
        sheep.velocity.copy(sheep.mesh.position).sub(this.wolf.position).setY(0).normalize().multiplyScalar(2.8);
        sheep.turnIn = .5;
      } else if (sheep.turnIn <= 0) {
        const angle = random(0, Math.PI * 2);
        sheep.velocity.set(Math.cos(angle), 0, Math.sin(angle)).multiplyScalar(random(.25, .7));
        sheep.turnIn = random(1.2, 4.5);
      }
      sheep.mesh.position.addScaledVector(sheep.velocity, dt);
      if (Math.abs(sheep.mesh.position.x) > MAP_W / 2 - 1.4) sheep.velocity.x *= -1;
      if (Math.abs(sheep.mesh.position.z) > MAP_H / 2 - 1.4) sheep.velocity.z *= -1;
      sheep.mesh.position.x = THREE.MathUtils.clamp(sheep.mesh.position.x, -MAP_W / 2 + 1.2, MAP_W / 2 - 1.2);
      sheep.mesh.position.z = THREE.MathUtils.clamp(sheep.mesh.position.z, -MAP_H / 2 + 1.2, MAP_H / 2 - 1.2);
      if (sheep.velocity.lengthSq() > .01) sheep.mesh.rotation.y = Math.atan2(-sheep.velocity.z, sheep.velocity.x);
    }
  }

  private updateDog(dt: number): void {
    const toWolf = this.wolf.position.clone().sub(this.dog.position).setY(0);
    const distance = toWolf.length();
    const night = this.phase === 'Ночь' || this.phase === 'Сумерки';
    const detection = this.disguised ? (night ? 4.2 : 2.2) : (night ? 12 : 8);
    let target: THREE.Vector3;
    let speed: number;
    if (distance < detection) {
      target = this.wolf.position;
      speed = night ? 5.1 : 4.2;
    } else {
      const angle = this.elapsed * (night ? .42 : .25);
      target = new THREE.Vector3(Math.cos(angle) * 10, 0, Math.sin(angle) * 7);
      speed = night ? 3.2 : 2.2;
    }
    const direction = target.clone().sub(this.dog.position).setY(0);
    if (direction.lengthSq() > .01) {
      direction.normalize();
      this.dog.position.addScaledVector(direction, speed * dt);
      this.dog.rotation.y = Math.atan2(-direction.z, direction.x);
    }
    if (distance < 1.25 && this.biteCooldown <= 0) {
      this.maxHealth = Math.max(0, this.maxHealth - 1);
      this.health = Math.min(this.health - 1, this.maxHealth);
      this.biteCooldown = 1.35;
      this.playTone(105, .2, .075, 'sawtooth');
      this.wolf.position.addScaledVector(toWolf.normalize(), 1.4);
      if (this.health <= 0) this.finish(false, 'Пёс раскрыл волка', 'Каждый укус оставляет постоянную рану. В следующий раз чаще возвращайтесь в стадо и меняйте облик заранее.');
    }
  }

  private tryEatSheep(): void {
    if (!this.keys.has('Space') || this.actionCooldown > 0 || this.disguised) return;
    let nearest: Sheep | undefined;
    let nearestDistance = 1.65;
    for (const sheep of this.sheep) {
      if (!sheep.alive) continue;
      const distance = sheep.mesh.position.distanceTo(this.wolf.position);
      if (distance < nearestDistance) {
        nearest = sheep;
        nearestDistance = distance;
      }
    }
    if (!nearest) return;
    nearest.alive = false;
    nearest.mesh.visible = false;
    this.score += 1;
    this.playTone(245 + this.score * 55, .16, .06);
    this.actionCooldown = 1.1;
    this.keys.delete('Space');
    if (this.score >= GOAL) this.finish(true, 'Идеальная охота', 'Вы добыли нужное количество овец и пережили смену ролей. Забег завершён.');
  }

  private updatePhase(): void {
    const t = this.elapsed % CYCLE_TIME;
    if (t < 50) this.phase = 'День';
    else if (t < 60) this.phase = 'Сумерки';
    else if (t < 110) this.phase = 'Ночь';
    else this.phase = 'Рассвет';

    const nightFactor = this.phase === 'Ночь' ? 1 : this.phase === 'Сумерки' || this.phase === 'Рассвет' ? .5 : 0;
    const day = new THREE.Color(0xaacb8b);
    const night = new THREE.Color(0x121b2b);
    const color = day.clone().lerp(night, nightFactor);
    this.scene.background = color;
    if (this.scene.fog instanceof THREE.Fog) this.scene.fog.color.copy(color);
    this.sun.intensity = THREE.MathUtils.lerp(2.1, .35, nightFactor);
    this.sky.intensity = THREE.MathUtils.lerp(1.6, .45, nightFactor);
  }

  private updateCamera(dt: number): void {
    this.cameraTarget.lerp(this.wolf.position, 1 - Math.exp(-3 * dt));
    this.camera.position.x = this.cameraTarget.x + 18;
    this.camera.position.z = this.cameraTarget.z + 18;
    this.camera.lookAt(this.cameraTarget);
  }

  private updateUi(): void {
    const seconds = Math.floor(this.elapsed % CYCLE_TIME);
    ui.phase.textContent = this.phase;
    ui.time.textContent = `${String(Math.floor(seconds / 60)).padStart(2, '0')}:${String(seconds % 60).padStart(2, '0')}`;
    ui.sheep.textContent = `Добыча: ${this.score} / ${GOAL}`;
    ui.health.textContent = `Здоровье: ${this.health} / ${this.maxHealth}`;
    ui.form.textContent = `Маскировка: ${this.disguised ? 'надета' : 'снята'}`;
    ui.progress.style.width = `${Math.min(100, this.changeProgress / CHANGE_TIME * 100)}%`;

    const distance = this.dog.position.distanceTo(this.wolf.position);
    const danger = distance < 3 ? 'критическое' : distance < 7 ? 'высокое' : 'низкое';
    ui.danger.textContent = `Подозрение: ${danger}`;
    if (this.changeProgress > 0) ui.hint.textContent = `Переодевание: ${Math.ceil(CHANGE_TIME - this.changeProgress)} с`;
    else if (!this.disguised) ui.hint.textContent = 'Пробел рядом с овцой — забрать добычу';
    else if (this.phase === 'Ночь') ui.hint.textContent = 'Ночью пёс ищет активнее. Не отходите от стада';
    else ui.hint.textContent = 'Удерживайте F неподвижно, чтобы снять маскировку';
  }

  private finish(won: boolean, title: string, text: string): void {
    this.running = false;
    this.finished = true;
    ui.overlayTitle.textContent = title;
    ui.overlayText.textContent = text;
    ui.start.textContent = won ? 'Сыграть ещё раз' : 'Попробовать снова';
    ui.overlay.classList.remove('hidden');
    this.playTone(won ? 659 : 130, .35, .065, won ? 'sine' : 'sawtooth');
  }

  private ensureAudio(): void {
    if (!this.audioContext) this.audioContext = new AudioContext();
    if (this.audioContext.state === 'suspended') void this.audioContext.resume();
  }

  private playTone(frequency: number, duration: number, volume: number, type: OscillatorType = 'sine'): void {
    if (!this.soundEnabled || !this.audioContext) return;
    const oscillator = this.audioContext.createOscillator();
    const gain = this.audioContext.createGain();
    oscillator.type = type;
    oscillator.frequency.value = frequency;
    gain.gain.setValueAtTime(volume, this.audioContext.currentTime);
    gain.gain.exponentialRampToValueAtTime(.0001, this.audioContext.currentTime + duration);
    oscillator.connect(gain).connect(this.audioContext.destination);
    oscillator.start();
    oscillator.stop(this.audioContext.currentTime + duration);
  }

  private showIntro(): void {
    ui.overlayTitle.textContent = 'Волк в овечьей шкуре';
    ui.overlayText.textContent = 'Днём смешивайтесь со стадом и выбирайте момент для охоты. Ночью сторожевой пёс становится активнее — теперь охотятся уже на вас.';
    ui.start.textContent = 'Начать забег';
    ui.overlay.classList.remove('hidden');
  }

  private resetSheep(): void {
    for (const sheep of this.sheep) {
      sheep.alive = true;
      sheep.mesh.visible = true;
      sheep.mesh.position.set(random(-12, 9), 0, random(-8, 8));
      sheep.velocity.set(0, 0, 0);
      sheep.turnIn = random(0, 2);
    }
  }

  private resize(): void {
    const aspect = window.innerWidth / window.innerHeight;
    const view = 18;
    this.camera.left = -view * aspect;
    this.camera.right = view * aspect;
    this.camera.top = view;
    this.camera.bottom = -view;
    this.camera.updateProjectionMatrix();
    this.renderer.setSize(window.innerWidth, window.innerHeight);
  }
}

function random(min: number, max: number): number {
  return min + Math.random() * (max - min);
}

new PrototypeGame(required('game'));
