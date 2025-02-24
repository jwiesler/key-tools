import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.kotlin.jvm") version "1.5.31" apply (false)
    id("org.jetbrains.dokka") version "1.6.10" apply (false)
    `maven-publish`
    `java-library`
}

repositories {
    mavenCentral()
}

subprojects {
    apply(plugin = "org.jetbrains.kotlin.jvm")
    apply(plugin = "org.jetbrains.dokka")
    apply(plugin = "maven-publish")
    apply(plugin = "java-library")

    val plugin by configurations.creating
    configurations {
        implementation.get().extendsFrom(plugin)
    }


    repositories {
        mavenCentral()
        maven { url = uri("https://maven.pkg.jetbrains.space/public/p/kotlinx-html/maven") }
        maven("https://git.key-project.org/api/v4/projects/35/packages/maven")
    }

    dependencies {
        val implementation by configurations

        val plugin by configurations
        plugin(platform("org.jetbrains.kotlin:kotlin-bom"))
        plugin("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
        plugin("com.github.ajalt:clikt:2.8.0")
        plugin("org.jetbrains:annotations:23.0.0")
        plugin("org.slf4j:slf4j-api:1.7.33")

        //    implementation("org.key_project:key.core")

        val testImplementation by configurations
        testImplementation("org.junit.jupiter:junit-jupiter-api:5.8.2")
        testImplementation("org.junit.jupiter:junit-jupiter-params:5.8.2")
        testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine:5.8.2")
        testImplementation("com.google.truth:truth:1.1.3")
        testImplementation("org.slf4j:slf4j-simple:1.7.33")
    }

    tasks.withType<KotlinCompile> {
        kotlinOptions {
            freeCompilerArgs = listOf("-Xjsr305=strict")
            jvmTarget = "11"
        }
    }

    tasks.withType<JavaCompile> {
        options.release.set(11)
    }

    tasks.withType<Test> {
        useJUnitPlatform()
        reports.html.required.set(false)
        reports.junitXml.required.set(true)
        testLogging {
            events("passed", "skipped", "failed")
            showExceptions = true
        }
    }

    java {
        withJavadocJar()
        withSourcesJar()
    }

    tasks.withType<Javadoc>()  {
        isFailOnError = false
    }


    publishing {
        publications {
            create<MavenPublication>("mavenJava") {
                from(components["java"])
                pom {
                    url.set("http://github.com/wadoon/key-tools")
                    licenses {
                        license {
                            name.set("GPLv2+")
                            url.set("https://www.gnu.org/licenses/old-licenses/gpl-2.0.html")
                        }
                    }
                    developers {
                        developer {
                            id.set("weigl")
                            name.set("Alexander Weigl ")
                            email.set("weigl@kit.edu")
                        }
                    }
                    scm {
                        connection.set("scm:git:https://github.com/wadoon/key-tools.git")
                        developerConnection.set("scm:git:git@github.com:wadoon/key-tools.git")
                        url.set("http://github.com/wadoon/key-tools")
                    }
                }
            }
            repositories {
                maven {
                    name = "GitHubPackages"
                    url = uri("https://maven.pkg.github.com/wadoon/key-tools")
                    credentials {
                        username = System.getenv("GITHUB_ACTOR")
                        password = System.getenv("GITHUB_TOKEN")
                    }
                }
            }
        }
    }
}
